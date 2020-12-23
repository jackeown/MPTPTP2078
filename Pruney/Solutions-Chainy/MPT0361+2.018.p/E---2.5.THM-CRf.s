%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:21 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 177 expanded)
%              Number of clauses        :   50 (  81 expanded)
%              Number of leaves         :   14 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  161 ( 386 expanded)
%              Number of equality atoms :   23 (  64 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t41_subset_1])).

fof(c_0_15,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X26,X25)
        | r1_tarski(X26,X24)
        | X25 != k1_zfmisc_1(X24) )
      & ( ~ r1_tarski(X27,X24)
        | r2_hidden(X27,X25)
        | X25 != k1_zfmisc_1(X24) )
      & ( ~ r2_hidden(esk1_2(X28,X29),X29)
        | ~ r1_tarski(esk1_2(X28,X29),X28)
        | X29 = k1_zfmisc_1(X28) )
      & ( r2_hidden(esk1_2(X28,X29),X29)
        | r1_tarski(esk1_2(X28,X29),X28)
        | X29 = k1_zfmisc_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_16,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X32,X31)
        | r2_hidden(X32,X31)
        | v1_xboole_0(X31) )
      & ( ~ r2_hidden(X32,X31)
        | m1_subset_1(X32,X31)
        | v1_xboole_0(X31) )
      & ( ~ m1_subset_1(X32,X31)
        | v1_xboole_0(X32)
        | ~ v1_xboole_0(X31) )
      & ( ~ v1_xboole_0(X32)
        | m1_subset_1(X32,X31)
        | ~ v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_18,plain,(
    ! [X35] : ~ v1_xboole_0(k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X11,X12] : r1_tarski(k4_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_26]),c_0_22])).

fof(c_0_31,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(k4_xboole_0(X19,X20),X21)
      | r1_tarski(X19,k2_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X22,X23] : r1_tarski(X22,k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k3_subset_1(X33,X34) = k4_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_39])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_51,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | ~ m1_subset_1(X38,k1_zfmisc_1(X36))
      | k4_subset_1(X36,X37,X38) = k2_xboole_0(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_52,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))
    | ~ r1_tarski(X2,k2_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_46])).

fof(c_0_56,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,k2_xboole_0(X17,X18))
      | r1_tarski(k4_xboole_0(X16,X17),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_21])])).

cnf(c_0_59,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk2_0,k4_xboole_0(X1,esk4_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_43])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_55])).

cnf(c_0_65,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_46])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_26]),c_0_21])])).

cnf(c_0_68,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_60])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(k4_xboole_0(X1,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,esk3_0))
    | ~ r1_tarski(esk2_0,X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_33])).

cnf(c_0_74,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_50]),c_0_68])])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_22])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_43]),c_0_73])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_73]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:07:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.47  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.028 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t41_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 0.19/0.47  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.47  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.47  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.47  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.47  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.47  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.19/0.47  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.47  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.47  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.47  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.47  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.19/0.47  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.19/0.47  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.19/0.47  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t41_subset_1])).
% 0.19/0.47  fof(c_0_15, plain, ![X24, X25, X26, X27, X28, X29]:(((~r2_hidden(X26,X25)|r1_tarski(X26,X24)|X25!=k1_zfmisc_1(X24))&(~r1_tarski(X27,X24)|r2_hidden(X27,X25)|X25!=k1_zfmisc_1(X24)))&((~r2_hidden(esk1_2(X28,X29),X29)|~r1_tarski(esk1_2(X28,X29),X28)|X29=k1_zfmisc_1(X28))&(r2_hidden(esk1_2(X28,X29),X29)|r1_tarski(esk1_2(X28,X29),X28)|X29=k1_zfmisc_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.47  fof(c_0_16, plain, ![X31, X32]:(((~m1_subset_1(X32,X31)|r2_hidden(X32,X31)|v1_xboole_0(X31))&(~r2_hidden(X32,X31)|m1_subset_1(X32,X31)|v1_xboole_0(X31)))&((~m1_subset_1(X32,X31)|v1_xboole_0(X32)|~v1_xboole_0(X31))&(~v1_xboole_0(X32)|m1_subset_1(X32,X31)|~v1_xboole_0(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.47  fof(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.47  fof(c_0_18, plain, ![X35]:~v1_xboole_0(k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.47  cnf(c_0_19, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_20, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_22, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.47  fof(c_0_23, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.47  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.47  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.19/0.47  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_27, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  cnf(c_0_28, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.47  fof(c_0_29, plain, ![X11, X12]:r1_tarski(k4_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.47  cnf(c_0_30, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_26]), c_0_22])).
% 0.19/0.47  fof(c_0_31, plain, ![X19, X20, X21]:(~r1_tarski(k4_xboole_0(X19,X20),X21)|r1_tarski(X19,k2_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.19/0.47  cnf(c_0_32, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.47  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.47  fof(c_0_34, plain, ![X22, X23]:r1_tarski(X22,k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.47  cnf(c_0_35, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_30])).
% 0.19/0.47  cnf(c_0_36, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.47  cnf(c_0_37, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.47  fof(c_0_38, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.47  cnf(c_0_39, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.47  fof(c_0_40, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.47  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_35])).
% 0.19/0.47  cnf(c_0_42, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.47  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.47  fof(c_0_44, plain, ![X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|k3_subset_1(X33,X34)=k4_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.47  cnf(c_0_45, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),X3)))), inference(spm,[status(thm)],[c_0_36, c_0_39])).
% 0.19/0.47  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.47  cnf(c_0_47, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_33])).
% 0.19/0.47  cnf(c_0_48, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.47  cnf(c_0_49, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_50, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.47  fof(c_0_51, plain, ![X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|~m1_subset_1(X38,k1_zfmisc_1(X36))|k4_subset_1(X36,X37,X38)=k2_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.19/0.47  fof(c_0_52, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.19/0.47  cnf(c_0_53, plain, (r1_tarski(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))|~r1_tarski(X2,k2_xboole_0(k4_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.47  cnf(c_0_54, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_47])).
% 0.19/0.47  cnf(c_0_55, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_46])).
% 0.19/0.47  fof(c_0_56, plain, ![X16, X17, X18]:(~r1_tarski(X16,k2_xboole_0(X17,X18))|r1_tarski(k4_xboole_0(X16,X17),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.19/0.47  cnf(c_0_57, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_39, c_0_43])).
% 0.19/0.47  cnf(c_0_58, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_21])])).
% 0.19/0.47  cnf(c_0_59, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.47  cnf(c_0_60, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.47  cnf(c_0_61, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_62, negated_conjecture, (r1_tarski(X1,k2_xboole_0(esk2_0,k4_xboole_0(X1,esk4_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_43])).
% 0.19/0.47  cnf(c_0_63, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_46, c_0_43])).
% 0.19/0.47  cnf(c_0_64, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,esk3_0)|~r1_tarski(esk2_0,X2)), inference(spm,[status(thm)],[c_0_27, c_0_55])).
% 0.19/0.47  cnf(c_0_65, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.47  cnf(c_0_66, plain, (r1_tarski(X1,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_57, c_0_46])).
% 0.19/0.47  cnf(c_0_67, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_26]), c_0_21])])).
% 0.19/0.47  cnf(c_0_68, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_33, c_0_60])).
% 0.19/0.47  cnf(c_0_69, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_70, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_61])).
% 0.19/0.47  cnf(c_0_71, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(k4_xboole_0(X1,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.47  cnf(c_0_72, negated_conjecture, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,esk3_0))|~r1_tarski(esk2_0,X3)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.47  cnf(c_0_73, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_66, c_0_33])).
% 0.19/0.47  cnf(c_0_74, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_50]), c_0_68])])).
% 0.19/0.47  cnf(c_0_75, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_22])).
% 0.19/0.47  cnf(c_0_76, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_43]), c_0_73])])).
% 0.19/0.47  cnf(c_0_77, negated_conjecture, (~r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.47  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_73]), c_0_77]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 79
% 0.19/0.47  # Proof object clause steps            : 50
% 0.19/0.47  # Proof object formula steps           : 29
% 0.19/0.47  # Proof object conjectures             : 28
% 0.19/0.47  # Proof object clause conjectures      : 25
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 18
% 0.19/0.47  # Proof object initial formulas used   : 14
% 0.19/0.47  # Proof object generating inferences   : 30
% 0.19/0.47  # Proof object simplifying inferences  : 17
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 14
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 22
% 0.19/0.47  # Removed in clause preprocessing      : 0
% 0.19/0.47  # Initial clauses in saturation        : 22
% 0.19/0.47  # Processed clauses                    : 1334
% 0.19/0.47  # ...of these trivial                  : 58
% 0.19/0.47  # ...subsumed                          : 888
% 0.19/0.47  # ...remaining for further processing  : 388
% 0.19/0.47  # Other redundant clauses eliminated   : 2
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 18
% 0.19/0.47  # Backward-rewritten                   : 20
% 0.19/0.47  # Generated clauses                    : 7246
% 0.19/0.47  # ...of the previous two non-trivial   : 5745
% 0.19/0.47  # Contextual simplify-reflections      : 3
% 0.19/0.47  # Paramodulations                      : 7242
% 0.19/0.47  # Factorizations                       : 2
% 0.19/0.47  # Equation resolutions                 : 2
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 326
% 0.19/0.47  #    Positive orientable unit clauses  : 71
% 0.19/0.47  #    Positive unorientable unit clauses: 4
% 0.19/0.47  #    Negative unit clauses             : 25
% 0.19/0.47  #    Non-unit-clauses                  : 226
% 0.19/0.47  # Current number of unprocessed clauses: 4402
% 0.19/0.47  # ...number of literals in the above   : 9814
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 60
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 21058
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 16095
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 534
% 0.19/0.47  # Unit Clause-clause subsumption calls : 1856
% 0.19/0.47  # Rewrite failures with RHS unbound    : 3
% 0.19/0.47  # BW rewrite match attempts            : 193
% 0.19/0.47  # BW rewrite match successes           : 34
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 78489
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.128 s
% 0.19/0.47  # System time              : 0.008 s
% 0.19/0.47  # Total time               : 0.136 s
% 0.19/0.47  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
