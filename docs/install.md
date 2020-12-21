# Install

## Docker container
A container images is available on Docker Hub. You can pull and launch it with:
`docker run -ti --rm ercoppa/fuzzolic-runner-v1`

## Manual build
Fuzzolic and fuzzy-sat have been tested on Ubuntu 18.04/20.04 x86_64. Please, step-by-step instruction for compiling them can be found inside the [`Dockerfile`](https://github.com/season-lab/fuzzolic/blob/master/docker/fuzzolic-runner/Dockerfile).

## Running tests
To test your installation of fuzzolic and fuzzy-sat, you can run some tests from the root of project:
`make tests`
