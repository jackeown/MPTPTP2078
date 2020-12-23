%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:29 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 182 expanded)
%              Number of clauses        :   49 (  89 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  174 ( 484 expanded)
%              Number of equality atoms :   28 (  88 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t38_zfmisc_1])).

fof(c_0_11,negated_conjecture,
    ( ( ~ r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)
      | ~ r2_hidden(esk2_0,esk4_0)
      | ~ r2_hidden(esk3_0,esk4_0) )
    & ( r2_hidden(esk2_0,esk4_0)
      | r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0) )
    & ( r2_hidden(esk3_0,esk4_0)
      | r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_12,plain,(
    ! [X29,X30] : k2_tarski(X29,X30) = k2_xboole_0(k1_tarski(X29),k1_tarski(X30)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_13,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | ~ r1_tarski(X22,X23)
      | r1_tarski(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | r1_tarski(X18,k2_xboole_0(X20,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_20,plain,(
    ! [X31,X32] :
      ( ( ~ r1_tarski(k1_tarski(X31),X32)
        | r2_hidden(X31,X32) )
      & ( ~ r2_hidden(X31,X32)
        | r1_tarski(k1_tarski(X31),X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | r2_hidden(esk2_0,esk4_0)
    | ~ r1_tarski(X1,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(X26,X27)
      | r1_tarski(k2_xboole_0(X26,X28),k2_xboole_0(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_15])).

fof(c_0_29,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_30,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)
    | r1_tarski(k1_tarski(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k2_xboole_0(X1,X2))
    | ~ r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k2_xboole_0(X4,X3))
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),esk4_0)
    | r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_36])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1)
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)
    | ~ r2_hidden(esk2_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k2_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2))
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_41,c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_52,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,X1) = X1
    | r2_hidden(esk1_3(X1,X1,X1),X1) ),
    inference(ef,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_15])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r1_tarski(k1_tarski(X1),k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k2_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(esk4_0,X2))
    | ~ r1_tarski(X1,k1_tarski(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
    | ~ r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_34])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)
    | ~ r1_tarski(k1_tarski(esk3_0),esk4_0)
    | ~ r2_hidden(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk3_0),X1),k2_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_40])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_43])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)
    | ~ r2_hidden(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_50])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(ef,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk3_0),X1),k2_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_36])).

cnf(c_0_67,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_32])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_36]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:55:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.53  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.53  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.53  #
% 0.20/0.53  # Preprocessing time       : 0.027 s
% 0.20/0.53  # Presaturation interreduction done
% 0.20/0.53  
% 0.20/0.53  # Proof found!
% 0.20/0.53  # SZS status Theorem
% 0.20/0.53  # SZS output start CNFRefutation
% 0.20/0.53  fof(t38_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.20/0.53  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.53  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.53  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.20/0.53  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.53  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.20/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.53  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 0.20/0.53  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.53  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.53  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t38_zfmisc_1])).
% 0.20/0.53  fof(c_0_11, negated_conjecture, ((~r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)|(~r2_hidden(esk2_0,esk4_0)|~r2_hidden(esk3_0,esk4_0)))&((r2_hidden(esk2_0,esk4_0)|r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0))&(r2_hidden(esk3_0,esk4_0)|r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.20/0.53  fof(c_0_12, plain, ![X29, X30]:k2_tarski(X29,X30)=k2_xboole_0(k1_tarski(X29),k1_tarski(X30)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.53  fof(c_0_13, plain, ![X21, X22, X23]:(~r1_tarski(X21,X22)|~r1_tarski(X22,X23)|r1_tarski(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.53  cnf(c_0_14, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.53  cnf(c_0_15, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.53  fof(c_0_16, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|r1_tarski(X18,k2_xboole_0(X20,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.20/0.53  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.53  cnf(c_0_18, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.53  fof(c_0_19, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.53  fof(c_0_20, plain, ![X31, X32]:((~r1_tarski(k1_tarski(X31),X32)|r2_hidden(X31,X32))&(~r2_hidden(X31,X32)|r1_tarski(k1_tarski(X31),X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.20/0.53  cnf(c_0_21, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.53  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.53  cnf(c_0_23, negated_conjecture, (r1_tarski(X1,esk4_0)|r2_hidden(esk2_0,esk4_0)|~r1_tarski(X1,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.53  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.53  cnf(c_0_25, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.53  fof(c_0_26, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.53  fof(c_0_27, plain, ![X26, X27, X28]:(~r1_tarski(X26,X27)|r1_tarski(k2_xboole_0(X26,X28),k2_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 0.20/0.53  cnf(c_0_28, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)), inference(rw,[status(thm)],[c_0_21, c_0_15])).
% 0.20/0.53  fof(c_0_29, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.53  fof(c_0_30, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.53  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 0.20/0.53  cnf(c_0_32, negated_conjecture, (r1_tarski(k1_tarski(esk2_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.20/0.53  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.53  cnf(c_0_34, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.53  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)|r1_tarski(k1_tarski(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_28])).
% 0.20/0.53  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.53  cnf(c_0_37, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.53  cnf(c_0_38, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.53  cnf(c_0_39, negated_conjecture, (r1_tarski(k1_tarski(esk2_0),k2_xboole_0(X1,X2))|~r1_tarski(esk4_0,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.53  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33])).
% 0.20/0.53  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,k2_xboole_0(X4,X3))|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_17, c_0_34])).
% 0.20/0.53  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_tarski(esk3_0),esk4_0)|r1_tarski(X1,esk4_0)|~r1_tarski(X1,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)))), inference(spm,[status(thm)],[c_0_17, c_0_35])).
% 0.20/0.53  cnf(c_0_43, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_24, c_0_36])).
% 0.20/0.53  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X1)|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_37])).
% 0.20/0.53  cnf(c_0_45, negated_conjecture, (~r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)|~r2_hidden(esk2_0,esk4_0)|~r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.53  cnf(c_0_46, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_38])).
% 0.20/0.53  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.53  cnf(c_0_48, negated_conjecture, (r1_tarski(k1_tarski(esk2_0),k2_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.53  cnf(c_0_49, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2))|~r1_tarski(X4,X3)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_41, c_0_34])).
% 0.20/0.53  cnf(c_0_50, negated_conjecture, (r1_tarski(k1_tarski(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.53  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.53  cnf(c_0_52, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.53  cnf(c_0_53, plain, (k2_xboole_0(X1,X1)=X1|r2_hidden(esk1_3(X1,X1,X1),X1)), inference(ef,[status(thm)],[c_0_44])).
% 0.20/0.53  cnf(c_0_54, negated_conjecture, (~r2_hidden(esk2_0,esk4_0)|~r2_hidden(esk3_0,esk4_0)|~r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)), inference(rw,[status(thm)],[c_0_45, c_0_15])).
% 0.20/0.53  cnf(c_0_55, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r1_tarski(k1_tarski(X1),k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.53  cnf(c_0_56, negated_conjecture, (r1_tarski(k1_tarski(esk2_0),k2_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_48, c_0_36])).
% 0.20/0.53  cnf(c_0_57, negated_conjecture, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(esk4_0,X2))|~r1_tarski(X1,k1_tarski(esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.53  cnf(c_0_58, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)|~r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_51, c_0_34])).
% 0.20/0.53  cnf(c_0_59, plain, (k2_xboole_0(X1,X1)=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_53])).
% 0.20/0.53  cnf(c_0_60, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)|~r1_tarski(k1_tarski(esk3_0),esk4_0)|~r2_hidden(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_47])).
% 0.20/0.53  cnf(c_0_61, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.53  cnf(c_0_62, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk3_0),X1),k2_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_57, c_0_40])).
% 0.20/0.53  cnf(c_0_63, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_43])])).
% 0.20/0.53  cnf(c_0_64, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)|~r2_hidden(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_50])])).
% 0.20/0.53  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(ef,[status(thm)],[c_0_61])).
% 0.20/0.53  cnf(c_0_66, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk3_0),X1),k2_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_62, c_0_36])).
% 0.20/0.53  cnf(c_0_67, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_63, c_0_32])).
% 0.20/0.53  cnf(c_0_68, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65])])).
% 0.20/0.53  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_36]), c_0_68]), ['proof']).
% 0.20/0.53  # SZS output end CNFRefutation
% 0.20/0.53  # Proof object total steps             : 70
% 0.20/0.53  # Proof object clause steps            : 49
% 0.20/0.53  # Proof object formula steps           : 21
% 0.20/0.53  # Proof object conjectures             : 27
% 0.20/0.53  # Proof object clause conjectures      : 24
% 0.20/0.53  # Proof object formula conjectures     : 3
% 0.20/0.53  # Proof object initial clauses used    : 16
% 0.20/0.53  # Proof object initial formulas used   : 10
% 0.20/0.53  # Proof object generating inferences   : 27
% 0.20/0.53  # Proof object simplifying inferences  : 14
% 0.20/0.53  # Training examples: 0 positive, 0 negative
% 0.20/0.53  # Parsed axioms                        : 10
% 0.20/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.53  # Initial clauses                      : 20
% 0.20/0.53  # Removed in clause preprocessing      : 1
% 0.20/0.53  # Initial clauses in saturation        : 19
% 0.20/0.53  # Processed clauses                    : 1772
% 0.20/0.53  # ...of these trivial                  : 152
% 0.20/0.53  # ...subsumed                          : 1087
% 0.20/0.53  # ...remaining for further processing  : 533
% 0.20/0.53  # Other redundant clauses eliminated   : 5
% 0.20/0.53  # Clauses deleted for lack of memory   : 0
% 0.20/0.53  # Backward-subsumed                    : 36
% 0.20/0.53  # Backward-rewritten                   : 153
% 0.20/0.53  # Generated clauses                    : 11132
% 0.20/0.53  # ...of the previous two non-trivial   : 9824
% 0.20/0.53  # Contextual simplify-reflections      : 6
% 0.20/0.53  # Paramodulations                      : 11044
% 0.20/0.53  # Factorizations                       : 80
% 0.20/0.53  # Equation resolutions                 : 8
% 0.20/0.53  # Propositional unsat checks           : 0
% 0.20/0.53  #    Propositional check models        : 0
% 0.20/0.53  #    Propositional check unsatisfiable : 0
% 0.20/0.53  #    Propositional clauses             : 0
% 0.20/0.53  #    Propositional clauses after purity: 0
% 0.20/0.53  #    Propositional unsat core size     : 0
% 0.20/0.53  #    Propositional preprocessing time  : 0.000
% 0.20/0.53  #    Propositional encoding time       : 0.000
% 0.20/0.53  #    Propositional solver time         : 0.000
% 0.20/0.53  #    Success case prop preproc time    : 0.000
% 0.20/0.53  #    Success case prop encoding time   : 0.000
% 0.20/0.53  #    Success case prop solver time     : 0.000
% 0.20/0.53  # Current number of processed clauses  : 324
% 0.20/0.53  #    Positive orientable unit clauses  : 59
% 0.20/0.53  #    Positive unorientable unit clauses: 1
% 0.20/0.53  #    Negative unit clauses             : 2
% 0.20/0.53  #    Non-unit-clauses                  : 262
% 0.20/0.53  # Current number of unprocessed clauses: 7589
% 0.20/0.53  # ...number of literals in the above   : 20241
% 0.20/0.53  # Current number of archived formulas  : 0
% 0.20/0.53  # Current number of archived clauses   : 208
% 0.20/0.53  # Clause-clause subsumption calls (NU) : 52600
% 0.20/0.53  # Rec. Clause-clause subsumption calls : 47624
% 0.20/0.53  # Non-unit clause-clause subsumptions  : 1112
% 0.20/0.53  # Unit Clause-clause subsumption calls : 412
% 0.20/0.53  # Rewrite failures with RHS unbound    : 0
% 0.20/0.53  # BW rewrite match attempts            : 380
% 0.20/0.53  # BW rewrite match successes           : 46
% 0.20/0.53  # Condensation attempts                : 0
% 0.20/0.53  # Condensation successes               : 0
% 0.20/0.53  # Termbank termtop insertions          : 137488
% 0.20/0.53  
% 0.20/0.53  # -------------------------------------------------
% 0.20/0.53  # User time                : 0.184 s
% 0.20/0.53  # System time              : 0.007 s
% 0.20/0.53  # Total time               : 0.190 s
% 0.20/0.53  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
