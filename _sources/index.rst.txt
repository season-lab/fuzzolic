.. Documentation of Fuzzolic

==================================================
fuzzing + concolic = fuzzolic :)
==================================================

.. raw:: html

    <p><a href="https://app.circleci.com/pipelines/github/season-lab/fuzzolic"><img src="https://circleci.com/gh/season-lab/fuzzolic.svg?style=shield" /></a><br /></p>

News
=======

* FUZZOLIC and FUZZY-SAT have been recently tested by FuzzBench: `report <https://www.fuzzbench.com/reports/experimental/2021-07-03-symbolic/index.html>`_.
* Thr preprint of the article accepted at COSE is available `here <https://github.com/ecoppa/ecoppa.github.io/raw/master/assets/pdf/FUZZOLIC-PREPRINT-COSE21.pdf>`_.
* The preprint of the paper accepted at ICSE is available on `ArXiv <https://arxiv.org/pdf/2102.06580>`_.
* **The code of FUZZOLIC and FUZZY-SAT has been released.**

Publications
=======

FUZZY-SAT
-------------

* Luca Borzacchiello, Emilio Coppa, and Camil Demetrescu. Fuzzing Symbolic Expressions. Proceedings of the 43rd International Conference on Software Engineering (ICSE 2021), 2021. `[PDF] <https://arxiv.org/pdf/2102.06580>`_

.. code-block:: latex

   @inproceedings{FUZZYSAT-ICSE21,
    author={Borzacchiello, Luca and Coppa, Emilio and Demetrescu, Camil},
    title={{Fuzzing Symbolic Expressions}},
    booktitle={Proceedings of the 43rd International Conference on Software Engineering},
    series={ICSE '21},
    doi={10.1109/ICSE43902.2021.00071},
    year={2021},
   }
   
FUZZOLIC
-------------

* Luca Borzacchiello, Emilio Coppa, and Camil Demetrescu. FUZZOLIC: mixing fuzzing and concolic execution. Computers & Security (COSE 2021), Elsevier, 2021.  `[PDF] <https://github.com/ecoppa/ecoppa.github.io/raw/master/assets/pdf/FUZZOLIC-PREPRINT-COSE21.pdf>`_

.. code-block:: latex

   @article{FUZZOLIC-COSE21,
    author={Borzacchiello, Luca and Coppa, Emilio and Demetrescu, Camil},
    title={{FUZZOLIC: mixing fuzzing and concolic execution}},
    journal={Computers & Security},
    publisher={Elsevier},
    doi={10.1016/j.cose.2021.102368},
    year={2021},
   }

.. toctree::
   :maxdepth: 2
   :caption: Getting Started
   
   install
   usage

.. toctree::
   :maxdepth: 2
   :caption: Development
   
   internals
   debug
   Source code Fuzzolic <https://github.com/season-lab/fuzzolic>
   Source code Fuzzy-SAT <https://github.com/season-lab/fuzzy-sat>
   
.. toctree::
   :maxdepth: 1
   :caption: Other
   
   icse-experiments
   


