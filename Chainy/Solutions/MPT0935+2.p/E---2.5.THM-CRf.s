%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0935+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:58 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 180 expanded)
%              Number of clauses        :   15 (  65 expanded)
%              Number of leaves         :   10 (  57 expanded)
%              Depth                    :    5
%              Number of atoms          :   48 ( 204 expanded)
%              Number of equality atoms :   38 ( 185 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t96_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X4,X5,X6)))) = k2_tarski(X1,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_mcart_1)).

fof(t24_relat_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( v1_relat_1(X5)
     => ( X5 = k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))
       => ( k1_relat_1(X5) = k2_tarski(X1,X3)
          & k2_relat_1(X5) = k2_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t24_relat_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(fc7_relat_1,axiom,(
    ! [X1,X2,X3,X4] : v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',fc7_relat_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X4,X5,X6)))) = k2_tarski(X1,X4) ),
    inference(assume_negation,[status(cth)],[t96_mcart_1])).

fof(c_0_11,plain,(
    ! [X252,X253,X254,X255,X256] :
      ( ( k1_relat_1(X256) = k2_tarski(X252,X254)
        | X256 != k2_tarski(k4_tarski(X252,X253),k4_tarski(X254,X255))
        | ~ v1_relat_1(X256) )
      & ( k2_relat_1(X256) = k2_tarski(X253,X255)
        | X256 != k2_tarski(k4_tarski(X252,X253),k4_tarski(X254,X255))
        | ~ v1_relat_1(X256) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relat_1])])])).

fof(c_0_12,plain,(
    ! [X110,X111] : k1_enumset1(X110,X110,X111) = k2_tarski(X110,X111) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X1555,X1556,X1557] : k2_enumset1(X1555,X1555,X1556,X1557) = k1_enumset1(X1555,X1556,X1557) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X1558,X1559,X1560,X1561] : k3_enumset1(X1558,X1558,X1559,X1560,X1561) = k2_enumset1(X1558,X1559,X1560,X1561) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,plain,(
    ! [X1698,X1699,X1700,X1701,X1702] : k4_enumset1(X1698,X1698,X1699,X1700,X1701,X1702) = k3_enumset1(X1698,X1699,X1700,X1701,X1702) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_16,plain,(
    ! [X1923,X1924,X1925,X1926,X1927,X1928] : k5_enumset1(X1923,X1923,X1924,X1925,X1926,X1927,X1928) = k4_enumset1(X1923,X1924,X1925,X1926,X1927,X1928) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_17,plain,(
    ! [X2000,X2001,X2002,X2003,X2004,X2005,X2006] : k6_enumset1(X2000,X2000,X2001,X2002,X2003,X2004,X2005,X2006) = k5_enumset1(X2000,X2001,X2002,X2003,X2004,X2005,X2006) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_18,plain,(
    ! [X248,X249,X250,X251] : v1_relat_1(k2_tarski(k4_tarski(X248,X249),k4_tarski(X250,X251))) ),
    inference(variable_rename,[status(thm)],[fc7_relat_1])).

fof(c_0_19,negated_conjecture,(
    k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk4_0,esk5_0,esk6_0)))) != k2_tarski(esk1_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_20,plain,(
    ! [X650,X651,X652] : k3_mcart_1(X650,X651,X652) = k4_tarski(k4_tarski(X650,X651),X652) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_21,plain,
    ( k1_relat_1(X1) = k2_tarski(X2,X3)
    | X1 != k2_tarski(k4_tarski(X2,X4),k4_tarski(X3,X5))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk4_0,esk5_0,esk6_0)))) != k2_tarski(esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k1_relat_1(X1) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)
    | X1 != k6_enumset1(k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X3,X5))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_32,plain,
    ( v1_relat_1(k6_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0)))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_34,plain,
    ( k1_relat_1(k6_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_32])])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
