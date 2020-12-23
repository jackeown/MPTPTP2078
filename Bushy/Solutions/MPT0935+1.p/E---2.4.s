%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t96_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:16 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   16 (  26 expanded)
%              Number of clauses        :    7 (  11 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  46 expanded)
%              Number of equality atoms :   18 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t96_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X4,X5,X6)))) = k2_tarski(X1,X4) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t96_mcart_1.p',t96_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t96_mcart_1.p',d3_mcart_1)).

fof(t24_relat_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( v1_relat_1(X5)
     => ( X5 = k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))
       => ( k1_relat_1(X5) = k2_tarski(X1,X3)
          & k2_relat_1(X5) = k2_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t96_mcart_1.p',t24_relat_1)).

fof(fc7_relat_1,axiom,(
    ! [X1,X2,X3,X4] : v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t96_mcart_1.p',fc7_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X4,X5,X6)))) = k2_tarski(X1,X4) ),
    inference(assume_negation,[status(cth)],[t96_mcart_1])).

fof(c_0_5,negated_conjecture,(
    k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk4_0,esk5_0,esk6_0)))) != k2_tarski(esk1_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X17,X18,X19] : k3_mcart_1(X17,X18,X19) = k4_tarski(k4_tarski(X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_7,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( k1_relat_1(X28) = k2_tarski(X24,X26)
        | X28 != k2_tarski(k4_tarski(X24,X25),k4_tarski(X26,X27))
        | ~ v1_relat_1(X28) )
      & ( k2_relat_1(X28) = k2_tarski(X25,X27)
        | X28 != k2_tarski(k4_tarski(X24,X25),k4_tarski(X26,X27))
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relat_1])])])).

fof(c_0_8,plain,(
    ! [X36,X37,X38,X39] : v1_relat_1(k2_tarski(k4_tarski(X36,X37),k4_tarski(X38,X39))) ),
    inference(variable_rename,[status(thm)],[fc7_relat_1])).

cnf(c_0_9,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk4_0,esk5_0,esk6_0)))) != k2_tarski(esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_relat_1(X1) = k2_tarski(X2,X3)
    | X1 != k2_tarski(k4_tarski(X2,X4),k4_tarski(X3,X5))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0)))) != k2_tarski(esk1_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_10])).

cnf(c_0_14,plain,
    ( k1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) = k2_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
