%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t89_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:15 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   29 (  59 expanded)
%              Number of clauses        :   14 (  32 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   78 ( 204 expanded)
%              Number of equality atoms :   77 ( 203 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t89_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k17_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X1
      & k18_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X2
      & k19_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X4
      & k20_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X5 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t89_mcart_1.p',t89_mcart_1)).

fof(d2_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k2_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t89_mcart_1.p',d2_mcart_1)).

fof(d14_mcart_1,axiom,(
    ! [X1] : k17_mcart_1(X1) = k1_mcart_1(k1_mcart_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t89_mcart_1.p',d14_mcart_1)).

fof(d15_mcart_1,axiom,(
    ! [X1] : k18_mcart_1(X1) = k2_mcart_1(k1_mcart_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t89_mcart_1.p',d15_mcart_1)).

fof(d16_mcart_1,axiom,(
    ! [X1] : k19_mcart_1(X1) = k1_mcart_1(k2_mcart_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t89_mcart_1.p',d16_mcart_1)).

fof(d17_mcart_1,axiom,(
    ! [X1] : k20_mcart_1(X1) = k2_mcart_1(k2_mcart_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t89_mcart_1.p',d17_mcart_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t89_mcart_1.p',d1_mcart_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k17_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X1
        & k18_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X2
        & k19_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X4
        & k20_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X5 ) ),
    inference(assume_negation,[status(cth)],[t89_mcart_1])).

fof(c_0_8,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32] :
      ( ( X29 != k2_mcart_1(X26)
        | X26 != k4_tarski(X30,X31)
        | X29 = X31
        | X26 != k4_tarski(X27,X28) )
      & ( X26 = k4_tarski(esk9_2(X26,X32),esk10_2(X26,X32))
        | X32 = k2_mcart_1(X26)
        | X26 != k4_tarski(X27,X28) )
      & ( X32 != esk10_2(X26,X32)
        | X32 = k2_mcart_1(X26)
        | X26 != k4_tarski(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

fof(c_0_9,negated_conjecture,
    ( k17_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk1_0
    | k18_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk2_0
    | k19_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk4_0
    | k20_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X13] : k17_mcart_1(X13) = k1_mcart_1(k1_mcart_1(X13)) ),
    inference(variable_rename,[status(thm)],[d14_mcart_1])).

fof(c_0_11,plain,(
    ! [X14] : k18_mcart_1(X14) = k2_mcart_1(k1_mcart_1(X14)) ),
    inference(variable_rename,[status(thm)],[d15_mcart_1])).

fof(c_0_12,plain,(
    ! [X15] : k19_mcart_1(X15) = k1_mcart_1(k2_mcart_1(X15)) ),
    inference(variable_rename,[status(thm)],[d16_mcart_1])).

fof(c_0_13,plain,(
    ! [X16] : k20_mcart_1(X16) = k2_mcart_1(k2_mcart_1(X16)) ),
    inference(variable_rename,[status(thm)],[d17_mcart_1])).

cnf(c_0_14,plain,
    ( X1 = X4
    | X1 != k2_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23] :
      ( ( X20 != k1_mcart_1(X17)
        | X17 != k4_tarski(X21,X22)
        | X20 = X21
        | X17 != k4_tarski(X18,X19) )
      & ( X17 = k4_tarski(esk7_2(X17,X23),esk8_2(X17,X23))
        | X23 = k1_mcart_1(X17)
        | X17 != k4_tarski(X18,X19) )
      & ( X23 != esk7_2(X17,X23)
        | X23 = k1_mcart_1(X17)
        | X17 != k4_tarski(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( k17_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk1_0
    | k18_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk2_0
    | k19_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk4_0
    | k20_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k17_mcart_1(X1) = k1_mcart_1(k1_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k18_mcart_1(X1) = k2_mcart_1(k1_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k19_mcart_1(X1) = k1_mcart_1(k2_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k20_mcart_1(X1) = k2_mcart_1(k2_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X4,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).

cnf(c_0_22,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( k1_mcart_1(k2_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))) != esk4_0
    | k2_mcart_1(k2_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))) != esk5_0
    | k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))) != esk1_0
    | k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).

cnf(c_0_26,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))) != esk1_0
    | k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))) != esk2_0
    | k1_mcart_1(k4_tarski(esk4_0,esk5_0)) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_24])])).

cnf(c_0_27,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27]),c_0_27]),c_0_24]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
