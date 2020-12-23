%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t57_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:11 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 829 expanded)
%              Number of clauses        :   32 ( 304 expanded)
%              Number of leaves         :    3 ( 200 expanded)
%              Depth                    :   15
%              Number of atoms          :  135 (4285 expanded)
%              Number of equality atoms :  134 (4284 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t57_mcart_1.p',t57_mcart_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t57_mcart_1.p',t55_mcart_1)).

fof(t56_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | X4 = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t57_mcart_1.p',t56_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_mcart_1])).

fof(c_0_4,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X25,X26,X27,X28] :
      ( ( X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | k4_zfmisc_1(X25,X26,X27,X28) != k1_xboole_0 )
      & ( X25 != k1_xboole_0
        | k4_zfmisc_1(X25,X26,X27,X28) = k1_xboole_0 )
      & ( X26 != k1_xboole_0
        | k4_zfmisc_1(X25,X26,X27,X28) = k1_xboole_0 )
      & ( X27 != k1_xboole_0
        | k4_zfmisc_1(X25,X26,X27,X28) = k1_xboole_0 )
      & ( X28 != k1_xboole_0
        | k4_zfmisc_1(X25,X26,X27,X28) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

fof(c_0_6,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36] :
      ( ( X29 = X33
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | k4_zfmisc_1(X29,X30,X31,X32) != k4_zfmisc_1(X33,X34,X35,X36) )
      & ( X30 = X34
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | k4_zfmisc_1(X29,X30,X31,X32) != k4_zfmisc_1(X33,X34,X35,X36) )
      & ( X31 = X35
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | k4_zfmisc_1(X29,X30,X31,X32) != k4_zfmisc_1(X33,X34,X35,X36) )
      & ( X32 = X36
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | k4_zfmisc_1(X29,X30,X31,X32) != k4_zfmisc_1(X33,X34,X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_mcart_1])])])).

cnf(c_0_7,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( k4_zfmisc_1(X2,X1,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 = k1_xboole_0
    | k4_zfmisc_1(X3,X4,X5,X1) != k4_zfmisc_1(X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_10]),c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_11]),c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_12]),c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( esk8_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X2,X3,X4,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_7]),c_0_14]),c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( esk8_0 = esk4_0 ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_20,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | k4_zfmisc_1(X1,X3,X4,X5) != k4_zfmisc_1(X2,X6,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk4_0) = k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_7,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( esk5_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( esk5_0 = esk1_0 ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_25,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k1_xboole_0
    | k4_zfmisc_1(X3,X4,X1,X5) != k4_zfmisc_1(X6,X7,X2,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk6_0,esk7_0,esk4_0) = k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( esk7_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X2,X3,X1,X4) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_22]),c_0_15]),c_0_27]),c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_30,negated_conjecture,
    ( esk7_0 = esk3_0 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_19])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | k4_zfmisc_1(X3,X1,X4,X5) != k4_zfmisc_1(X6,X2,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk6_0,esk3_0,esk4_0) = k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_24])])).

cnf(c_0_36,negated_conjecture,
    ( esk6_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X2,X1,X3,X4) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22]),c_0_34]),c_0_27]),c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( esk6_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
