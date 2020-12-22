#!/usr/bin/python3

import pytest


def pytest_addoption(parser):
    parser.addoption("--fuzzy", action="store_true", default="run tests using Fuzzy-SAT")


@pytest.fixture
def fuzzy(request):
    return request.config.getoption("--fuzzy")
