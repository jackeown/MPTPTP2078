%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0865+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:19 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   16 (  22 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  54 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_mcart_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(t8_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,X2)
         => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t23_mcart_1])).

fof(c_0_4,plain,(
    ! [X5,X6,X9,X11,X12] :
      ( ( ~ v1_relat_1(X5)
        | ~ r2_hidden(X6,X5)
        | X6 = k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)) )
      & ( r2_hidden(esk3_1(X9),X9)
        | v1_relat_1(X9) )
      & ( esk3_1(X9) != k4_tarski(X11,X12)
        | v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r2_hidden(esk4_0,esk5_0)
    & esk4_0 != k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X13,X14,X15] :
      ( X13 != k4_tarski(X14,X15)
      | k4_tarski(k1_mcart_1(X13),k2_mcart_1(X13)) = X13 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_mcart_1])])])).

cnf(c_0_7,plain,
    ( X2 = k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k4_tarski(esk1_2(esk5_0,X1),esk2_2(esk5_0,X1)) = X1
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( k4_tarski(k1_mcart_1(k4_tarski(X1,X2)),k2_mcart_1(k4_tarski(X1,X2))) = k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( k4_tarski(esk1_2(esk5_0,esk4_0),esk2_2(esk5_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( esk4_0 != k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),
    [proof]).

%------------------------------------------------------------------------------
