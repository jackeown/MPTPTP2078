%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:52 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 531 expanded)
%              Number of clauses        :   59 ( 238 expanded)
%              Number of leaves         :    7 ( 126 expanded)
%              Depth                    :   21
%              Number of atoms          :  202 (1975 expanded)
%              Number of equality atoms :   22 ( 273 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ( X1 != k1_xboole_0
           => m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,X1)
       => ! [X3] :
            ( m1_subset_1(X3,X1)
           => ( X1 != k1_xboole_0
             => m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_subset_1])).

fof(c_0_8,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X18,X17)
        | r2_hidden(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ r2_hidden(X18,X17)
        | m1_subset_1(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ m1_subset_1(X18,X17)
        | v1_xboole_0(X18)
        | ~ v1_xboole_0(X17) )
      & ( ~ v1_xboole_0(X18)
        | m1_subset_1(X18,X17)
        | ~ v1_xboole_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_9,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0)
    & m1_subset_1(esk4_0,esk2_0)
    & esk2_0 != k1_xboole_0
    & ~ m1_subset_1(k2_tarski(esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_10,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_14,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | r1_tarski(X9,X7)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r1_tarski(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | ~ r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_15,plain,(
    ! [X14,X15,X16] :
      ( ( r2_hidden(X14,X16)
        | ~ r1_tarski(k2_tarski(X14,X15),X16) )
      & ( r2_hidden(X15,X16)
        | ~ r1_tarski(k2_tarski(X14,X15),X16) )
      & ( ~ r2_hidden(X14,X16)
        | ~ r2_hidden(X15,X16)
        | r1_tarski(k2_tarski(X14,X15),X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_16,plain,(
    ! [X5,X6] : k1_enumset1(X5,X5,X6) = k2_tarski(X5,X6) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(X1,esk4_0)
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_19,plain,(
    ! [X19] : ~ v1_xboole_0(k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(X1,esk4_0)
    | r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,X1)
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(X1,esk4_0)
    | r2_hidden(esk4_0,esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_11])).

fof(c_0_30,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,X1)
    | r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(k1_enumset1(X1,X1,X2),k1_zfmisc_1(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(X1,esk4_0)
    | r2_hidden(esk4_0,esk2_0)
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_0,X1)
    | r2_hidden(esk4_0,esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_32])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_0,esk4_0)
    | r2_hidden(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0)
    | r2_hidden(esk4_0,esk2_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_0,X1)
    | r2_hidden(esk3_0,esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k1_enumset1(X1,X1,esk4_0),k1_zfmisc_1(esk2_0))
    | m1_subset_1(esk2_0,esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0)
    | r2_hidden(esk4_0,esk2_0)
    | r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0)
    | r2_hidden(esk3_0,esk2_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(k1_enumset1(esk3_0,esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k1_enumset1(X1,X1,esk4_0),k1_zfmisc_1(esk2_0))
    | m1_subset_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0)
    | r2_hidden(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_11])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0)
    | r2_hidden(esk3_0,esk2_0)
    | r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_32])])).

cnf(c_0_57,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_46]),c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k1_enumset1(X1,X1,esk4_0),k1_zfmisc_1(esk2_0))
    | m1_subset_1(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0)
    | r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_57]),c_0_11]),c_0_32])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_xboole_0(k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_63]),c_0_47])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_61]),c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_38])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( ~ m1_subset_1(k1_enumset1(esk3_0,esk3_0,k1_xboole_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_46]),c_0_47])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.32  % Computer   : n024.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 20:09:21 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  # Version: 2.5pre002
% 0.10/0.32  # No SInE strategy applied
% 0.10/0.32  # Trying AutoSched0 for 299 seconds
% 0.16/0.39  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.16/0.39  # and selection function SelectVGNonCR.
% 0.16/0.39  #
% 0.16/0.39  # Preprocessing time       : 0.017 s
% 0.16/0.39  # Presaturation interreduction done
% 0.16/0.39  
% 0.16/0.39  # Proof found!
% 0.16/0.39  # SZS status Theorem
% 0.16/0.39  # SZS output start CNFRefutation
% 0.16/0.39  fof(t56_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_subset_1)).
% 0.16/0.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.16/0.39  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.16/0.39  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.16/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.16/0.39  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.16/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.16/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t56_subset_1])).
% 0.16/0.39  fof(c_0_8, plain, ![X17, X18]:(((~m1_subset_1(X18,X17)|r2_hidden(X18,X17)|v1_xboole_0(X17))&(~r2_hidden(X18,X17)|m1_subset_1(X18,X17)|v1_xboole_0(X17)))&((~m1_subset_1(X18,X17)|v1_xboole_0(X18)|~v1_xboole_0(X17))&(~v1_xboole_0(X18)|m1_subset_1(X18,X17)|~v1_xboole_0(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.16/0.39  fof(c_0_9, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)&(m1_subset_1(esk4_0,esk2_0)&(esk2_0!=k1_xboole_0&~m1_subset_1(k2_tarski(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.16/0.39  cnf(c_0_10, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.39  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.39  cnf(c_0_12, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.39  cnf(c_0_13, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.16/0.39  fof(c_0_14, plain, ![X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X9,X8)|r1_tarski(X9,X7)|X8!=k1_zfmisc_1(X7))&(~r1_tarski(X10,X7)|r2_hidden(X10,X8)|X8!=k1_zfmisc_1(X7)))&((~r2_hidden(esk1_2(X11,X12),X12)|~r1_tarski(esk1_2(X11,X12),X11)|X12=k1_zfmisc_1(X11))&(r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(esk1_2(X11,X12),X11)|X12=k1_zfmisc_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.16/0.39  fof(c_0_15, plain, ![X14, X15, X16]:(((r2_hidden(X14,X16)|~r1_tarski(k2_tarski(X14,X15),X16))&(r2_hidden(X15,X16)|~r1_tarski(k2_tarski(X14,X15),X16)))&(~r2_hidden(X14,X16)|~r2_hidden(X15,X16)|r1_tarski(k2_tarski(X14,X15),X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.16/0.39  fof(c_0_16, plain, ![X5, X6]:k1_enumset1(X5,X5,X6)=k2_tarski(X5,X6), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.16/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(X1,esk4_0)|~v1_xboole_0(esk2_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.16/0.39  cnf(c_0_18, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.39  fof(c_0_19, plain, ![X19]:~v1_xboole_0(k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.16/0.39  cnf(c_0_20, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.39  cnf(c_0_21, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.16/0.39  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.39  cnf(c_0_23, negated_conjecture, (m1_subset_1(X1,esk4_0)|r2_hidden(X2,esk2_0)|~m1_subset_1(X2,esk2_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.16/0.39  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,X1)|~v1_xboole_0(esk2_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.16/0.39  cnf(c_0_25, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.16/0.39  cnf(c_0_26, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.39  cnf(c_0_27, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_20])).
% 0.16/0.39  cnf(c_0_28, plain, (r1_tarski(k1_enumset1(X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.16/0.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(X1,esk4_0)|r2_hidden(esk4_0,esk2_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_11])).
% 0.16/0.39  fof(c_0_30, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.16/0.39  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,X1)|r2_hidden(X2,esk2_0)|~m1_subset_1(X2,esk2_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.16/0.39  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.39  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.16/0.39  cnf(c_0_34, plain, (r2_hidden(k1_enumset1(X1,X1,X2),k1_zfmisc_1(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.16/0.39  cnf(c_0_35, negated_conjecture, (m1_subset_1(X1,esk4_0)|r2_hidden(esk4_0,esk2_0)|r2_hidden(X2,X1)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_18])).
% 0.16/0.39  cnf(c_0_36, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.16/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk4_0,X1)|r2_hidden(esk4_0,esk2_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_31, c_0_11])).
% 0.16/0.39  cnf(c_0_38, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_10, c_0_32])).
% 0.16/0.39  cnf(c_0_39, plain, (m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.16/0.39  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk2_0,esk4_0)|r2_hidden(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_11])).
% 0.16/0.39  cnf(c_0_41, negated_conjecture, (esk4_0=k1_xboole_0|~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_13])).
% 0.16/0.39  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)|r2_hidden(esk4_0,esk2_0)|~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.16/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk4_0,X1)|r2_hidden(esk3_0,esk2_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.16/0.39  cnf(c_0_44, negated_conjecture, (~m1_subset_1(k2_tarski(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.39  cnf(c_0_45, negated_conjecture, (m1_subset_1(k1_enumset1(X1,X1,esk4_0),k1_zfmisc_1(esk2_0))|m1_subset_1(esk2_0,esk4_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.16/0.39  cnf(c_0_46, plain, (X1=k1_xboole_0|r2_hidden(X2,X1)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_36, c_0_18])).
% 0.16/0.39  cnf(c_0_47, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.39  cnf(c_0_48, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(X1,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_18])).
% 0.16/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)|r2_hidden(esk4_0,esk2_0)|r2_hidden(X1,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_18])).
% 0.16/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)|r2_hidden(esk3_0,esk2_0)|~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_38])).
% 0.16/0.39  cnf(c_0_51, negated_conjecture, (~m1_subset_1(k1_enumset1(esk3_0,esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[c_0_44, c_0_22])).
% 0.16/0.39  cnf(c_0_52, negated_conjecture, (m1_subset_1(k1_enumset1(X1,X1,esk4_0),k1_zfmisc_1(esk2_0))|m1_subset_1(esk2_0,esk4_0)|~m1_subset_1(X1,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.16/0.39  cnf(c_0_53, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(esk2_0))|~m1_subset_1(X2,esk2_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_48])).
% 0.16/0.39  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)|r2_hidden(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_11])).
% 0.16/0.39  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)|r2_hidden(esk3_0,esk2_0)|r2_hidden(X1,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_18])).
% 0.16/0.39  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_32])])).
% 0.16/0.39  cnf(c_0_57, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(esk2_0))|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_46]), c_0_47])).
% 0.16/0.39  cnf(c_0_58, negated_conjecture, (m1_subset_1(k1_enumset1(X1,X1,esk4_0),k1_zfmisc_1(esk2_0))|m1_subset_1(esk4_0,esk3_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_54])).
% 0.16/0.39  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)|r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_55, c_0_32])).
% 0.16/0.39  cnf(c_0_60, negated_conjecture, (v1_xboole_0(esk2_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_10, c_0_56])).
% 0.16/0.39  cnf(c_0_61, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_57]), c_0_11]), c_0_32])])).
% 0.16/0.39  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_51])).
% 0.16/0.39  cnf(c_0_63, negated_conjecture, (v1_xboole_0(esk2_0)|~v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.16/0.39  cnf(c_0_64, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_10, c_0_62])).
% 0.16/0.39  cnf(c_0_65, negated_conjecture, (~v1_xboole_0(k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_63]), c_0_47])).
% 0.16/0.39  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_61]), c_0_65])).
% 0.16/0.39  cnf(c_0_67, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_66, c_0_38])).
% 0.16/0.39  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_67, c_0_18])).
% 0.16/0.39  cnf(c_0_69, negated_conjecture, (m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(esk2_0))|~m1_subset_1(X2,esk2_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_68])).
% 0.16/0.39  cnf(c_0_70, negated_conjecture, (~m1_subset_1(k1_enumset1(esk3_0,esk3_0,k1_xboole_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[c_0_51, c_0_61])).
% 0.16/0.39  cnf(c_0_71, negated_conjecture, (m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(esk2_0))|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_46]), c_0_47])).
% 0.16/0.39  cnf(c_0_72, negated_conjecture, (m1_subset_1(k1_xboole_0,esk2_0)), inference(rw,[status(thm)],[c_0_11, c_0_61])).
% 0.16/0.39  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_32])]), ['proof']).
% 0.16/0.39  # SZS output end CNFRefutation
% 0.16/0.39  # Proof object total steps             : 74
% 0.16/0.39  # Proof object clause steps            : 59
% 0.16/0.39  # Proof object formula steps           : 15
% 0.16/0.39  # Proof object conjectures             : 47
% 0.16/0.39  # Proof object clause conjectures      : 44
% 0.16/0.39  # Proof object formula conjectures     : 3
% 0.16/0.39  # Proof object initial clauses used    : 13
% 0.16/0.39  # Proof object initial formulas used   : 7
% 0.16/0.39  # Proof object generating inferences   : 40
% 0.16/0.39  # Proof object simplifying inferences  : 20
% 0.16/0.39  # Training examples: 0 positive, 0 negative
% 0.16/0.39  # Parsed axioms                        : 7
% 0.16/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.39  # Initial clauses                      : 18
% 0.16/0.39  # Removed in clause preprocessing      : 1
% 0.16/0.39  # Initial clauses in saturation        : 17
% 0.16/0.39  # Processed clauses                    : 813
% 0.16/0.39  # ...of these trivial                  : 29
% 0.16/0.39  # ...subsumed                          : 191
% 0.16/0.39  # ...remaining for further processing  : 593
% 0.16/0.39  # Other redundant clauses eliminated   : 0
% 0.16/0.39  # Clauses deleted for lack of memory   : 0
% 0.16/0.39  # Backward-subsumed                    : 83
% 0.16/0.39  # Backward-rewritten                   : 301
% 0.16/0.39  # Generated clauses                    : 6948
% 0.16/0.39  # ...of the previous two non-trivial   : 2931
% 0.16/0.39  # Contextual simplify-reflections      : 0
% 0.16/0.39  # Paramodulations                      : 6942
% 0.16/0.39  # Factorizations                       : 2
% 0.16/0.39  # Equation resolutions                 : 4
% 0.16/0.39  # Propositional unsat checks           : 0
% 0.16/0.39  #    Propositional check models        : 0
% 0.16/0.39  #    Propositional check unsatisfiable : 0
% 0.16/0.39  #    Propositional clauses             : 0
% 0.16/0.39  #    Propositional clauses after purity: 0
% 0.16/0.39  #    Propositional unsat core size     : 0
% 0.16/0.39  #    Propositional preprocessing time  : 0.000
% 0.16/0.39  #    Propositional encoding time       : 0.000
% 0.16/0.39  #    Propositional solver time         : 0.000
% 0.16/0.39  #    Success case prop preproc time    : 0.000
% 0.16/0.39  #    Success case prop encoding time   : 0.000
% 0.16/0.39  #    Success case prop solver time     : 0.000
% 0.16/0.39  # Current number of processed clauses  : 192
% 0.16/0.39  #    Positive orientable unit clauses  : 19
% 0.16/0.39  #    Positive unorientable unit clauses: 0
% 0.16/0.39  #    Negative unit clauses             : 6
% 0.16/0.39  #    Non-unit-clauses                  : 167
% 0.16/0.39  # Current number of unprocessed clauses: 1942
% 0.16/0.39  # ...number of literals in the above   : 7933
% 0.16/0.39  # Current number of archived formulas  : 0
% 0.16/0.39  # Current number of archived clauses   : 402
% 0.16/0.39  # Clause-clause subsumption calls (NU) : 39222
% 0.16/0.39  # Rec. Clause-clause subsumption calls : 20335
% 0.16/0.39  # Non-unit clause-clause subsumptions  : 184
% 0.16/0.39  # Unit Clause-clause subsumption calls : 2517
% 0.16/0.39  # Rewrite failures with RHS unbound    : 0
% 0.16/0.39  # BW rewrite match attempts            : 30
% 0.16/0.39  # BW rewrite match successes           : 12
% 0.16/0.39  # Condensation attempts                : 0
% 0.16/0.39  # Condensation successes               : 0
% 0.16/0.39  # Termbank termtop insertions          : 101831
% 0.16/0.39  
% 0.16/0.39  # -------------------------------------------------
% 0.16/0.39  # User time                : 0.060 s
% 0.16/0.39  # System time              : 0.009 s
% 0.16/0.39  # Total time               : 0.069 s
% 0.16/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
