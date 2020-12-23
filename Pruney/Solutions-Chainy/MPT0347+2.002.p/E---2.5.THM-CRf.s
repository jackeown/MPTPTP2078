%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:12 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 265 expanded)
%              Number of clauses        :   50 ( 121 expanded)
%              Number of leaves         :    6 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  200 (1496 expanded)
%              Number of equality atoms :   32 ( 252 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(X5,X2)
                    <=> ( r2_hidden(X5,X3)
                        & ~ r2_hidden(X5,X4) ) ) )
               => X2 = k7_subset_1(X1,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,X2)
                      <=> ( r2_hidden(X5,X3)
                          & ~ r2_hidden(X5,X4) ) ) )
                 => X2 = k7_subset_1(X1,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_subset_1])).

fof(c_0_7,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X20,X19)
        | r2_hidden(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ r2_hidden(X20,X19)
        | m1_subset_1(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ m1_subset_1(X20,X19)
        | v1_xboole_0(X20)
        | ~ v1_xboole_0(X19) )
      & ( ~ v1_xboole_0(X20)
        | m1_subset_1(X20,X19)
        | ~ v1_xboole_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ r2_hidden(X23,X22)
      | r2_hidden(X23,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_10,negated_conjecture,(
    ! [X31] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
      & ( r2_hidden(X31,esk5_0)
        | ~ r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & ( ~ r2_hidden(X31,esk6_0)
        | ~ r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & ( ~ r2_hidden(X31,esk5_0)
        | r2_hidden(X31,esk6_0)
        | r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & esk4_0 != k7_subset_1(esk3_0,esk5_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X13,X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | ~ r2_hidden(esk2_3(X15,X16,X17),X15)
        | r2_hidden(esk2_3(X15,X16,X17),X16)
        | X17 = k4_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X15)
        | r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X16)
        | r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k4_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_16])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

fof(c_0_28,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k7_subset_1(X24,X25,X26) = k4_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_22])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(esk6_0,X1) = esk6_0
    | r2_hidden(esk2_3(esk6_0,X1,esk6_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( X1 = k4_xboole_0(X2,esk6_0)
    | r2_hidden(esk2_3(X2,esk6_0,X1),esk4_0)
    | r2_hidden(esk2_3(X2,esk6_0,X1),X1)
    | ~ r2_hidden(esk2_3(X2,esk6_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( esk4_0 != k7_subset_1(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k4_xboole_0(X2,esk5_0)
    | r2_hidden(esk2_3(X2,esk5_0,X1),X1)
    | ~ r2_hidden(esk2_3(X2,esk5_0,X1),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_29]),c_0_30])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk6_0,X1) = esk6_0
    | ~ r2_hidden(esk2_3(esk6_0,X1,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_25]),c_0_34])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_25]),c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( X1 = k4_xboole_0(esk5_0,esk6_0)
    | r2_hidden(esk2_3(esk5_0,esk6_0,X1),esk4_0)
    | r2_hidden(esk2_3(esk5_0,esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk6_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_15])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( X1 = k4_xboole_0(esk4_0,esk5_0)
    | r2_hidden(esk2_3(esk4_0,esk5_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_17])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X1)
    | v1_xboole_0(k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk4_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_45]),c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( X1 = k4_xboole_0(esk4_0,esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_48])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk6_0)
    | ~ r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_52]),c_0_46])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_xboole_0(k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_52])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_55])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.36/0.52  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.36/0.52  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.36/0.52  #
% 0.36/0.52  # Preprocessing time       : 0.028 s
% 0.36/0.52  # Presaturation interreduction done
% 0.36/0.52  
% 0.36/0.52  # Proof found!
% 0.36/0.52  # SZS status Theorem
% 0.36/0.52  # SZS output start CNFRefutation
% 0.36/0.52  fof(t17_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,X2)<=>(r2_hidden(X5,X3)&~(r2_hidden(X5,X4)))))=>X2=k7_subset_1(X1,X3,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_subset_1)).
% 0.36/0.52  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.36/0.52  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.36/0.52  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.36/0.52  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.36/0.52  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.36/0.52  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,X2)<=>(r2_hidden(X5,X3)&~(r2_hidden(X5,X4)))))=>X2=k7_subset_1(X1,X3,X4)))))), inference(assume_negation,[status(cth)],[t17_subset_1])).
% 0.36/0.52  fof(c_0_7, plain, ![X19, X20]:(((~m1_subset_1(X20,X19)|r2_hidden(X20,X19)|v1_xboole_0(X19))&(~r2_hidden(X20,X19)|m1_subset_1(X20,X19)|v1_xboole_0(X19)))&((~m1_subset_1(X20,X19)|v1_xboole_0(X20)|~v1_xboole_0(X19))&(~v1_xboole_0(X20)|m1_subset_1(X20,X19)|~v1_xboole_0(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.36/0.52  fof(c_0_8, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.36/0.52  fof(c_0_9, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|(~r2_hidden(X23,X22)|r2_hidden(X23,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.36/0.52  fof(c_0_10, negated_conjecture, ![X31]:(m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))&((((r2_hidden(X31,esk5_0)|~r2_hidden(X31,esk4_0)|~m1_subset_1(X31,esk3_0))&(~r2_hidden(X31,esk6_0)|~r2_hidden(X31,esk4_0)|~m1_subset_1(X31,esk3_0)))&(~r2_hidden(X31,esk5_0)|r2_hidden(X31,esk6_0)|r2_hidden(X31,esk4_0)|~m1_subset_1(X31,esk3_0)))&esk4_0!=k7_subset_1(esk3_0,esk5_0,esk6_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).
% 0.36/0.52  fof(c_0_11, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:((((r2_hidden(X13,X10)|~r2_hidden(X13,X12)|X12!=k4_xboole_0(X10,X11))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|X12!=k4_xboole_0(X10,X11)))&(~r2_hidden(X14,X10)|r2_hidden(X14,X11)|r2_hidden(X14,X12)|X12!=k4_xboole_0(X10,X11)))&((~r2_hidden(esk2_3(X15,X16,X17),X17)|(~r2_hidden(esk2_3(X15,X16,X17),X15)|r2_hidden(esk2_3(X15,X16,X17),X16))|X17=k4_xboole_0(X15,X16))&((r2_hidden(esk2_3(X15,X16,X17),X15)|r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k4_xboole_0(X15,X16))&(~r2_hidden(esk2_3(X15,X16,X17),X16)|r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k4_xboole_0(X15,X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.36/0.52  cnf(c_0_12, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.36/0.52  cnf(c_0_13, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.36/0.52  cnf(c_0_14, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.36/0.52  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.36/0.52  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.36/0.52  cnf(c_0_17, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.36/0.52  cnf(c_0_18, negated_conjecture, (r2_hidden(X1,esk6_0)|r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.36/0.52  cnf(c_0_19, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_12, c_0_13])).
% 0.36/0.52  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.36/0.52  cnf(c_0_21, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.36/0.52  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.36/0.52  cnf(c_0_23, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.36/0.52  cnf(c_0_24, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_14, c_0_16])).
% 0.36/0.52  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_17])).
% 0.36/0.52  cnf(c_0_26, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.36/0.52  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,esk6_0)|r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.36/0.52  fof(c_0_28, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k7_subset_1(X24,X25,X26)=k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.36/0.52  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.36/0.52  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_22])).
% 0.36/0.52  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.36/0.52  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.36/0.52  cnf(c_0_33, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.36/0.52  cnf(c_0_34, negated_conjecture, (k4_xboole_0(esk6_0,X1)=esk6_0|r2_hidden(esk2_3(esk6_0,X1,esk6_0),esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.36/0.52  cnf(c_0_35, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.36/0.52  cnf(c_0_36, negated_conjecture, (X1=k4_xboole_0(X2,esk6_0)|r2_hidden(esk2_3(X2,esk6_0,X1),esk4_0)|r2_hidden(esk2_3(X2,esk6_0,X1),X1)|~r2_hidden(esk2_3(X2,esk6_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.36/0.52  cnf(c_0_37, negated_conjecture, (esk4_0!=k7_subset_1(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.36/0.52  cnf(c_0_38, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.36/0.52  cnf(c_0_39, negated_conjecture, (X1=k4_xboole_0(X2,esk5_0)|r2_hidden(esk2_3(X2,esk5_0,X1),X1)|~r2_hidden(esk2_3(X2,esk5_0,X1),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_29]), c_0_30])).
% 0.36/0.52  cnf(c_0_40, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_31])).
% 0.36/0.52  cnf(c_0_41, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.36/0.52  cnf(c_0_42, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_32])).
% 0.36/0.52  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk6_0,X1)=esk6_0|~r2_hidden(esk2_3(esk6_0,X1,esk6_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_25]), c_0_34])).
% 0.36/0.52  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_25]), c_0_25])).
% 0.36/0.52  cnf(c_0_45, negated_conjecture, (X1=k4_xboole_0(esk5_0,esk6_0)|r2_hidden(esk2_3(esk5_0,esk6_0,X1),esk4_0)|r2_hidden(esk2_3(esk5_0,esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_36, c_0_17])).
% 0.36/0.52  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk5_0,esk6_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_15])])).
% 0.36/0.52  cnf(c_0_47, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.36/0.52  cnf(c_0_48, negated_conjecture, (X1=k4_xboole_0(esk4_0,esk5_0)|r2_hidden(esk2_3(esk4_0,esk5_0,X1),X1)), inference(spm,[status(thm)],[c_0_39, c_0_17])).
% 0.36/0.52  cnf(c_0_49, plain, (v1_xboole_0(k4_xboole_0(X1,X2))|~r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.36/0.52  cnf(c_0_50, plain, (r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X1)|v1_xboole_0(k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 0.36/0.52  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk6_0,esk4_0)=esk6_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.36/0.52  cnf(c_0_52, negated_conjecture, (r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_45]), c_0_46])).
% 0.36/0.52  cnf(c_0_53, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_47])).
% 0.36/0.52  cnf(c_0_54, negated_conjecture, (X1=k4_xboole_0(esk4_0,esk5_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_13, c_0_48])).
% 0.36/0.52  cnf(c_0_55, plain, (v1_xboole_0(k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.36/0.52  cnf(c_0_56, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_51])).
% 0.36/0.52  cnf(c_0_57, negated_conjecture, (r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk6_0)|~r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_52]), c_0_46])).
% 0.36/0.52  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~v1_xboole_0(k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_13, c_0_53])).
% 0.36/0.52  cnf(c_0_59, negated_conjecture, (k4_xboole_0(X1,X1)=k4_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.36/0.52  cnf(c_0_60, negated_conjecture, (~r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_52])])).
% 0.36/0.52  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_55])])).
% 0.36/0.52  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_52])]), ['proof']).
% 0.36/0.52  # SZS output end CNFRefutation
% 0.36/0.52  # Proof object total steps             : 63
% 0.36/0.52  # Proof object clause steps            : 50
% 0.36/0.52  # Proof object formula steps           : 13
% 0.36/0.52  # Proof object conjectures             : 32
% 0.36/0.52  # Proof object clause conjectures      : 29
% 0.36/0.52  # Proof object formula conjectures     : 3
% 0.36/0.52  # Proof object initial clauses used    : 18
% 0.36/0.52  # Proof object initial formulas used   : 6
% 0.36/0.52  # Proof object generating inferences   : 31
% 0.36/0.52  # Proof object simplifying inferences  : 15
% 0.36/0.52  # Training examples: 0 positive, 0 negative
% 0.36/0.52  # Parsed axioms                        : 6
% 0.36/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.36/0.52  # Initial clauses                      : 21
% 0.36/0.52  # Removed in clause preprocessing      : 0
% 0.36/0.52  # Initial clauses in saturation        : 21
% 0.36/0.52  # Processed clauses                    : 3314
% 0.36/0.52  # ...of these trivial                  : 73
% 0.36/0.52  # ...subsumed                          : 2698
% 0.36/0.52  # ...remaining for further processing  : 543
% 0.36/0.52  # Other redundant clauses eliminated   : 25
% 0.36/0.52  # Clauses deleted for lack of memory   : 0
% 0.36/0.52  # Backward-subsumed                    : 54
% 0.36/0.52  # Backward-rewritten                   : 84
% 0.36/0.52  # Generated clauses                    : 8205
% 0.36/0.52  # ...of the previous two non-trivial   : 7766
% 0.36/0.52  # Contextual simplify-reflections      : 31
% 0.36/0.52  # Paramodulations                      : 8115
% 0.36/0.52  # Factorizations                       : 32
% 0.36/0.52  # Equation resolutions                 : 54
% 0.36/0.52  # Propositional unsat checks           : 0
% 0.36/0.52  #    Propositional check models        : 0
% 0.36/0.52  #    Propositional check unsatisfiable : 0
% 0.36/0.52  #    Propositional clauses             : 0
% 0.36/0.52  #    Propositional clauses after purity: 0
% 0.36/0.52  #    Propositional unsat core size     : 0
% 0.36/0.52  #    Propositional preprocessing time  : 0.000
% 0.36/0.52  #    Propositional encoding time       : 0.000
% 0.36/0.52  #    Propositional solver time         : 0.000
% 0.36/0.52  #    Success case prop preproc time    : 0.000
% 0.36/0.52  #    Success case prop encoding time   : 0.000
% 0.36/0.52  #    Success case prop solver time     : 0.000
% 0.36/0.52  # Current number of processed clauses  : 380
% 0.36/0.52  #    Positive orientable unit clauses  : 22
% 0.36/0.52  #    Positive unorientable unit clauses: 1
% 0.36/0.52  #    Negative unit clauses             : 11
% 0.36/0.52  #    Non-unit-clauses                  : 346
% 0.36/0.52  # Current number of unprocessed clauses: 4259
% 0.36/0.52  # ...number of literals in the above   : 14875
% 0.36/0.52  # Current number of archived formulas  : 0
% 0.36/0.52  # Current number of archived clauses   : 163
% 0.36/0.52  # Clause-clause subsumption calls (NU) : 25097
% 0.36/0.52  # Rec. Clause-clause subsumption calls : 19065
% 0.36/0.52  # Non-unit clause-clause subsumptions  : 1502
% 0.36/0.52  # Unit Clause-clause subsumption calls : 895
% 0.36/0.52  # Rewrite failures with RHS unbound    : 6
% 0.36/0.52  # BW rewrite match attempts            : 88
% 0.36/0.52  # BW rewrite match successes           : 18
% 0.36/0.52  # Condensation attempts                : 0
% 0.36/0.52  # Condensation successes               : 0
% 0.36/0.52  # Termbank termtop insertions          : 89301
% 0.36/0.52  
% 0.36/0.52  # -------------------------------------------------
% 0.36/0.52  # User time                : 0.162 s
% 0.36/0.52  # System time              : 0.012 s
% 0.36/0.52  # Total time               : 0.175 s
% 0.36/0.52  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
