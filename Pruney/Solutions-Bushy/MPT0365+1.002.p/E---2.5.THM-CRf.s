%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0365+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:30 EST 2020

% Result     : Theorem 10.35s
% Output     : CNFRefutation 10.35s
% Verified   : 
% Statistics : Number of formulae       :  119 (3525 expanded)
%              Number of clauses        :  106 (1775 expanded)
%              Number of leaves         :    6 ( 818 expanded)
%              Depth                    :   22
%              Number of atoms          :  267 (18255 expanded)
%              Number of equality atoms :   61 (4044 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ( r1_xboole_0(X2,X3)
              & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ( r1_xboole_0(X2,X3)
                & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
             => X2 = k3_subset_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_subset_1])).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_8,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r2_hidden(esk2_2(X20,X21),X20)
        | r1_xboole_0(X20,X21) )
      & ( r2_hidden(esk2_2(X20,X21),X21)
        | r1_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X25,X23)
        | ~ r2_hidden(X25,X24)
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_9,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & r1_xboole_0(esk4_0,esk5_0)
    & r1_xboole_0(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,esk5_0))
    & esk4_0 != k3_subset_1(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,X2))
    | ~ r2_hidden(esk2_2(X1,k4_xboole_0(esk5_0,X2)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_19,plain,(
    ! [X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | k3_subset_1(X5,X6) = k4_xboole_0(X5,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_20,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | m1_subset_1(k3_subset_1(X16,X17),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | k3_subset_1(X18,k3_subset_1(X18,X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(esk4_0,k4_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,X2))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_22])).

cnf(c_0_32,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k3_subset_1(X1,X2)) = k3_subset_1(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k3_subset_1(esk3_0,k3_subset_1(esk3_0,esk5_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(X1,k3_subset_1(esk3_0,esk5_0))
    | ~ r2_hidden(X1,k3_subset_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_29])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk5_0,X1) = k4_xboole_0(X2,X2)
    | ~ r2_hidden(esk1_3(X2,X2,k4_xboole_0(esk5_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,X2)),X3)
    | r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk3_0,k3_subset_1(esk3_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk3_0,esk5_0),X1)
    | ~ r2_hidden(esk2_2(k3_subset_1(esk3_0,esk5_0),X1),k3_subset_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X3)
    | ~ r2_hidden(esk1_3(X3,X3,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk5_0,X1) = k4_xboole_0(esk4_0,esk4_0)
    | r2_hidden(esk1_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,X1)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k3_subset_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk3_0,esk5_0),k4_xboole_0(k3_subset_1(esk3_0,esk4_0),X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_16])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk2_2(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( k3_subset_1(esk3_0,k3_subset_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk4_0) = k4_xboole_0(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( X1 = k4_xboole_0(esk5_0,X2)
    | r2_hidden(esk1_3(esk5_0,X2,X1),esk3_0)
    | r2_hidden(esk1_3(esk5_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) = k3_subset_1(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k3_subset_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(k3_subset_1(esk3_0,esk4_0),X2))
    | ~ r2_hidden(X1,k3_subset_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_47])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,X3))
    | r2_hidden(esk2_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_18])).

cnf(c_0_57,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_16])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk3_0,k3_subset_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_40]),c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_51]),c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( X1 = k4_xboole_0(esk5_0,esk3_0)
    | r2_hidden(esk1_3(esk5_0,esk3_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,k3_subset_1(esk3_0,esk5_0))
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk3_0,esk4_0),X1)
    | r2_hidden(esk2_2(k3_subset_1(esk3_0,esk4_0),X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk3_0,esk4_0),X1)
    | r2_hidden(esk2_2(k3_subset_1(esk3_0,esk4_0),X1),X2)
    | ~ r2_hidden(esk2_2(k3_subset_1(esk3_0,esk4_0),X1),k3_subset_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk5_0) = k4_xboole_0(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_24])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk3_0,esk4_0),X1)
    | r2_hidden(esk2_2(k3_subset_1(esk3_0,esk4_0),X1),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(esk5_0,X1)
    | ~ r2_hidden(esk2_2(esk5_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_18])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_64])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,k4_xboole_0(X4,X2)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_57])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_65])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk3_0,esk4_0),k4_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(esk5_0,k4_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_16])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk3_0),X2)
    | ~ r2_hidden(esk2_2(k4_xboole_0(X1,esk3_0),X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_18])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),k4_xboole_0(X4,X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk5_0,esk3_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(X1,k3_subset_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,k4_xboole_0(X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,X2))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_16])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k3_subset_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_53])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk1_3(X1,X2,X1),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( k4_xboole_0(k3_subset_1(esk3_0,esk4_0),X1) = k3_subset_1(esk3_0,esk4_0)
    | ~ r2_hidden(esk1_3(k3_subset_1(esk3_0,esk4_0),X1,k3_subset_1(esk3_0,esk4_0)),k4_xboole_0(X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_67])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk4_0,X1),X2) = k4_xboole_0(esk4_0,X1)
    | ~ r2_hidden(esk1_3(k4_xboole_0(esk4_0,X1),X2,k4_xboole_0(esk4_0,X1)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_67])).

cnf(c_0_87,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk4_0,X2))
    | ~ r2_hidden(esk2_2(X1,k4_xboole_0(esk4_0,X2)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_14])).

cnf(c_0_88,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))
    | r2_hidden(esk2_2(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_68,c_0_56])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,X2))
    | ~ r2_hidden(X1,k4_xboole_0(X3,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(X1,X2) = k3_subset_1(esk3_0,esk5_0)
    | r2_hidden(esk1_3(X1,X2,k3_subset_1(esk3_0,esk5_0)),esk3_0)
    | r2_hidden(esk1_3(X1,X2,k3_subset_1(esk3_0,esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_24])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_84,c_0_74])).

cnf(c_0_92,negated_conjecture,
    ( k4_xboole_0(k3_subset_1(esk3_0,esk4_0),k4_xboole_0(X1,esk5_0)) = k3_subset_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_74])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk4_0,X1),esk5_0) = k4_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_74])).

cnf(c_0_94,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_67])).

cnf(c_0_95,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(k3_subset_1(esk3_0,esk5_0),X2))
    | ~ r2_hidden(esk2_2(X1,k4_xboole_0(k3_subset_1(esk3_0,esk5_0),X2)),k3_subset_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_16])).

cnf(c_0_96,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(X1,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk4_0,X1),X2) = k3_subset_1(esk3_0,esk5_0)
    | ~ r2_hidden(esk1_3(k4_xboole_0(esk4_0,X1),X2,k3_subset_1(esk3_0,esk5_0)),k4_xboole_0(X3,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_36])).

cnf(c_0_98,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk5_0),k3_subset_1(esk3_0,esk4_0)) = k4_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_79])).

cnf(c_0_100,negated_conjecture,
    ( esk4_0 != k3_subset_1(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_101,negated_conjecture,
    ( k4_xboole_0(esk4_0,X1) = esk4_0
    | ~ r2_hidden(esk1_3(esk4_0,X1,esk4_0),k3_subset_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_58])).

cnf(c_0_102,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(k3_subset_1(esk3_0,esk5_0),k4_xboole_0(X1,k3_subset_1(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_88])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(X2,esk5_0)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_96])).

cnf(c_0_104,plain,
    ( X1 = k4_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X2,X3,X1),k4_xboole_0(X2,X4))
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | r2_hidden(esk1_3(X2,X3,X1),X4) ),
    inference(spm,[status(thm)],[c_0_48,c_0_24])).

cnf(c_0_105,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk4_0,k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,esk5_0)),k4_xboole_0(X1,esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),c_0_99]),c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( k4_xboole_0(X1,X2) = k3_subset_1(esk3_0,esk5_0)
    | r2_hidden(esk1_3(X1,X2,k3_subset_1(esk3_0,esk5_0)),k4_xboole_0(X1,X3))
    | r2_hidden(esk1_3(X1,X2,k3_subset_1(esk3_0,esk5_0)),esk3_0)
    | r2_hidden(esk1_3(X1,X2,k3_subset_1(esk3_0,esk5_0)),X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_90])).

cnf(c_0_107,negated_conjecture,
    ( k4_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_101,c_0_74])).

cnf(c_0_108,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(k3_subset_1(esk3_0,esk5_0),k4_xboole_0(X2,k3_subset_1(esk3_0,esk4_0))))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_102])).

cnf(c_0_109,plain,
    ( X1 = k4_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X2,X3,X1),k4_xboole_0(X1,X4))
    | r2_hidden(esk1_3(X2,X3,X1),X2)
    | r2_hidden(esk1_3(X2,X3,X1),X4) ),
    inference(spm,[status(thm)],[c_0_48,c_0_24])).

cnf(c_0_110,negated_conjecture,
    ( X1 = k4_xboole_0(esk4_0,X2)
    | r2_hidden(esk1_3(esk4_0,X2,X1),k4_xboole_0(X3,esk5_0))
    | r2_hidden(esk1_3(esk4_0,X2,X1),X1)
    | ~ r2_hidden(esk1_3(esk4_0,X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,esk5_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_100])).

cnf(c_0_112,negated_conjecture,
    ( k4_xboole_0(X1,X2) = k3_subset_1(esk3_0,esk5_0)
    | r2_hidden(esk1_3(X1,X2,k3_subset_1(esk3_0,esk5_0)),k4_xboole_0(X3,k3_subset_1(esk3_0,esk4_0)))
    | r2_hidden(esk1_3(X1,X2,k3_subset_1(esk3_0,esk5_0)),X1)
    | ~ r2_hidden(esk1_3(X1,X2,k3_subset_1(esk3_0,esk5_0)),X3) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_113,plain,
    ( ~ r2_hidden(X1,k3_subset_1(X2,k3_subset_1(X2,X3)))
    | ~ r2_hidden(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_33])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,esk5_0)),k3_subset_1(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_107]),c_0_53])]),c_0_100])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,esk5_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_111]),c_0_107]),c_0_58])]),c_0_100])).

cnf(c_0_116,plain,
    ( ~ r2_hidden(X1,k3_subset_1(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_27])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,esk5_0)),k3_subset_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_114]),c_0_107]),c_0_115])]),c_0_100])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_115]),c_0_40])]),
    [proof]).

%------------------------------------------------------------------------------
