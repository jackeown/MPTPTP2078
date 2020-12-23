%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0936+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:26 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  23 expanded)
%              Number of clauses        :    7 (  10 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  43 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t97_mcart_1,conjecture,(
    ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t23_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( X3 = k1_tarski(k4_tarski(X1,X2))
       => ( k1_relat_1(X3) = k1_tarski(X1)
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(fc5_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k1_tarski(k4_tarski(X1,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t97_mcart_1])).

fof(c_0_5,negated_conjecture,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0)))) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X4,X5,X6] : k3_mcart_1(X4,X5,X6) = k4_tarski(k4_tarski(X4,X5),X6) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_7,plain,(
    ! [X9,X10,X11] :
      ( ( k1_relat_1(X11) = k1_tarski(X9)
        | X11 != k1_tarski(k4_tarski(X9,X10))
        | ~ v1_relat_1(X11) )
      & ( k2_relat_1(X11) = k1_tarski(X10)
        | X11 != k1_tarski(k4_tarski(X9,X10))
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_relat_1])])])).

fof(c_0_8,plain,(
    ! [X7,X8] : v1_relat_1(k1_tarski(k4_tarski(X7,X8))) ),
    inference(variable_rename,[status(thm)],[fc5_relat_1])).

cnf(c_0_9,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0)))) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_relat_1(X1) = k1_tarski(X2)
    | X1 != k1_tarski(k4_tarski(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)))) != k1_tarski(esk1_0) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(X1,X2))) = k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])]),
    [proof]).

%------------------------------------------------------------------------------
