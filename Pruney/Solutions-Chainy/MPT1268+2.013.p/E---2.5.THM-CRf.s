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
% DateTime   : Thu Dec  3 11:12:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 562 expanded)
%              Number of clauses        :   56 ( 237 expanded)
%              Number of leaves         :   10 ( 140 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 (2540 expanded)
%              Number of equality atoms :   35 ( 358 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t86_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X1) )
                 => X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(c_0_10,plain,(
    ! [X10] : m1_subset_1(k1_subset_1(X10),k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_11,plain,(
    ! [X9] : k1_subset_1(X9) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_13,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | r1_tarski(k1_tops_1(X15,X16),X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | v3_pre_topc(k1_tops_1(X13,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_tops_1(X1,k1_xboole_0),X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tops_1(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X1) )
                   => X3 = k1_xboole_0 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_tops_1])).

fof(c_0_29,plain,(
    ! [X17,X18,X19] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
      | ~ v3_pre_topc(X18,X17)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(X18,k1_tops_1(X17,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( X1 = k1_tops_1(X2,k1_xboole_0)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,negated_conjecture,(
    ! [X25] :
      ( v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ v2_tops_1(esk2_0,esk1_0) )
      & ( r1_tarski(esk3_0,esk2_0)
        | ~ v2_tops_1(esk2_0,esk1_0) )
      & ( v3_pre_topc(esk3_0,esk1_0)
        | ~ v2_tops_1(esk2_0,esk1_0) )
      & ( esk3_0 != k1_xboole_0
        | ~ v2_tops_1(esk2_0,esk1_0) )
      & ( v2_tops_1(esk2_0,esk1_0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r1_tarski(X25,esk2_0)
        | ~ v3_pre_topc(X25,esk1_0)
        | X25 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])])])).

cnf(c_0_34,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_24])).

cnf(c_0_35,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_17])])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X20,X21] :
      ( ( ~ v2_tops_1(X21,X20)
        | k1_tops_1(X20,X21) = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( k1_tops_1(X20,X21) != k1_xboole_0
        | v2_tops_1(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_41,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_42,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_43,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( v2_tops_1(X2,X1)
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_49,negated_conjecture,
    ( k1_tops_1(esk1_0,X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_39])])).

cnf(c_0_50,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k1_xboole_0
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_39])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_44])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X1,k1_tops_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = k1_xboole_0
    | ~ v2_tops_1(esk3_0,esk1_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_45]),c_0_39])])).

cnf(c_0_54,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_46]),c_0_39])]),c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,plain,
    ( v2_tops_1(X1,X2)
    | k1_tops_1(X2,X1) != k1_xboole_0
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k1_tops_1(esk1_0,X1) = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_48]),c_0_23])).

cnf(c_0_58,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ v2_tops_1(esk2_0,esk1_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_50]),c_0_39]),c_0_44])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_44]),c_0_39])])).

cnf(c_0_63,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0)
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0)
    | ~ v3_pre_topc(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_tops_1(esk3_0,esk1_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( v2_tops_1(X1,esk1_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_39])]),c_0_23]),c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk3_0,k1_xboole_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_46]),c_0_60]),c_0_45])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( k1_tops_1(esk1_0,X1) = k1_xboole_0
    | v2_tops_1(esk2_0,esk1_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_31]),c_0_39]),c_0_38])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k1_xboole_0
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_44]),c_0_68])]),c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_36])).

cnf(c_0_74,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0)
    | k1_tops_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_44]),c_0_39])])).

cnf(c_0_75,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_48]),c_0_73])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:02:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.19/0.43  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.028 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(dt_k1_subset_1, axiom, ![X1]:m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 0.19/0.43  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.19/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.43  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.43  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.19/0.43  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.19/0.43  fof(t86_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 0.19/0.43  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 0.19/0.43  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 0.19/0.43  fof(c_0_10, plain, ![X10]:m1_subset_1(k1_subset_1(X10),k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[dt_k1_subset_1])).
% 0.19/0.43  fof(c_0_11, plain, ![X9]:k1_subset_1(X9)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.19/0.43  fof(c_0_12, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.43  cnf(c_0_13, plain, (m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_14, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.43  fof(c_0_15, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.43  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_17, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.43  fof(c_0_18, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.43  cnf(c_0_19, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_20, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.43  fof(c_0_21, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|r1_tarski(k1_tops_1(X15,X16),X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.19/0.43  cnf(c_0_22, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.43  cnf(c_0_24, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  fof(c_0_25, plain, ![X13, X14]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|v3_pre_topc(k1_tops_1(X13,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.19/0.43  cnf(c_0_26, plain, (X1=X2|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.43  cnf(c_0_27, plain, (r1_tarski(k1_tops_1(X1,k1_xboole_0),X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_17])])).
% 0.19/0.43  fof(c_0_28, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t86_tops_1])).
% 0.19/0.43  fof(c_0_29, plain, ![X17, X18, X19]:(~l1_pre_topc(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|(~v3_pre_topc(X18,X17)|~r1_tarski(X18,X19)|r1_tarski(X18,k1_tops_1(X17,X19)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.19/0.43  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_31, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.43  cnf(c_0_32, plain, (X1=k1_tops_1(X2,k1_xboole_0)|~l1_pre_topc(X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.43  fof(c_0_33, negated_conjecture, ![X25]:((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v2_tops_1(esk2_0,esk1_0))&(((r1_tarski(esk3_0,esk2_0)|~v2_tops_1(esk2_0,esk1_0))&(v3_pre_topc(esk3_0,esk1_0)|~v2_tops_1(esk2_0,esk1_0)))&(esk3_0!=k1_xboole_0|~v2_tops_1(esk2_0,esk1_0))))&(v2_tops_1(esk2_0,esk1_0)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk1_0)))|(~r1_tarski(X25,esk2_0)|~v3_pre_topc(X25,esk1_0)|X25=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])])])).
% 0.19/0.43  cnf(c_0_34, plain, (k1_tops_1(X1,X2)=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k1_tops_1(X1,X2))), inference(spm,[status(thm)],[c_0_22, c_0_24])).
% 0.19/0.43  cnf(c_0_35, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.43  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 0.19/0.43  cnf(c_0_37, plain, (v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_17])])).
% 0.19/0.43  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  fof(c_0_40, plain, ![X20, X21]:((~v2_tops_1(X21,X20)|k1_tops_1(X20,X21)=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))&(k1_tops_1(X20,X21)!=k1_xboole_0|v2_tops_1(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.19/0.43  cnf(c_0_41, plain, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.19/0.43  cnf(c_0_42, negated_conjecture, (v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.19/0.43  cnf(c_0_43, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.43  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v2_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_46, negated_conjecture, (v3_pre_topc(esk3_0,esk1_0)|~v2_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_47, plain, (v2_tops_1(X2,X1)|k1_tops_1(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.43  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_49, negated_conjecture, (k1_tops_1(esk1_0,X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_39])])).
% 0.19/0.43  cnf(c_0_50, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k1_xboole_0|~v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_39])])).
% 0.19/0.43  cnf(c_0_51, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_16, c_0_44])).
% 0.19/0.43  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r1_tarski(X1,k1_tops_1(X3,X2))), inference(spm,[status(thm)],[c_0_19, c_0_24])).
% 0.19/0.43  cnf(c_0_53, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=k1_xboole_0|~v2_tops_1(esk3_0,esk1_0)|~v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_45]), c_0_39])])).
% 0.19/0.43  cnf(c_0_54, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|~v2_tops_1(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_46]), c_0_39])]), c_0_45])).
% 0.19/0.43  cnf(c_0_55, negated_conjecture, (esk3_0!=k1_xboole_0|~v2_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_56, plain, (v2_tops_1(X1,X2)|k1_tops_1(X2,X1)!=k1_xboole_0|~l1_pre_topc(X2)|~r1_tarski(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.43  cnf(c_0_57, negated_conjecture, (k1_tops_1(esk1_0,X1)=X1|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_48]), c_0_23])).
% 0.19/0.43  cnf(c_0_58, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.19/0.43  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~v2_tops_1(esk2_0,esk1_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_50]), c_0_39]), c_0_44])])).
% 0.19/0.43  cnf(c_0_60, negated_conjecture, (r1_tarski(esk3_0,esk2_0)|~v2_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_61, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_51])).
% 0.19/0.43  cnf(c_0_62, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_44]), c_0_39])])).
% 0.19/0.43  cnf(c_0_63, negated_conjecture, (v2_tops_1(esk2_0,esk1_0)|X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)|~v3_pre_topc(X1,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_64, negated_conjecture, (~v2_tops_1(esk3_0,esk1_0)|~v2_tops_1(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.19/0.43  cnf(c_0_65, negated_conjecture, (v2_tops_1(X1,esk1_0)|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_39])]), c_0_23]), c_0_58])).
% 0.19/0.43  cnf(c_0_66, negated_conjecture, (r1_tarski(esk3_0,k1_xboole_0)|~v2_tops_1(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_46]), c_0_60]), c_0_45])).
% 0.19/0.43  cnf(c_0_67, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_61])).
% 0.19/0.43  cnf(c_0_68, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_36])).
% 0.19/0.43  cnf(c_0_69, negated_conjecture, (k1_tops_1(esk1_0,X1)=k1_xboole_0|v2_tops_1(esk2_0,esk1_0)|~m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_31]), c_0_39]), c_0_38])])).
% 0.19/0.43  cnf(c_0_70, negated_conjecture, (~v2_tops_1(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.19/0.43  cnf(c_0_71, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.43  cnf(c_0_72, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k1_xboole_0|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_44]), c_0_68])]), c_0_70])).
% 0.19/0.43  cnf(c_0_73, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_71, c_0_36])).
% 0.19/0.43  cnf(c_0_74, negated_conjecture, (v2_tops_1(esk2_0,esk1_0)|k1_tops_1(esk1_0,esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_44]), c_0_39])])).
% 0.19/0.43  cnf(c_0_75, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_48]), c_0_73])])).
% 0.19/0.43  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75])]), c_0_70]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 77
% 0.19/0.43  # Proof object clause steps            : 56
% 0.19/0.43  # Proof object formula steps           : 21
% 0.19/0.43  # Proof object conjectures             : 34
% 0.19/0.43  # Proof object clause conjectures      : 31
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 20
% 0.19/0.43  # Proof object initial formulas used   : 10
% 0.19/0.43  # Proof object generating inferences   : 33
% 0.19/0.43  # Proof object simplifying inferences  : 46
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 10
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 21
% 0.19/0.43  # Removed in clause preprocessing      : 1
% 0.19/0.43  # Initial clauses in saturation        : 20
% 0.19/0.43  # Processed clauses                    : 803
% 0.19/0.43  # ...of these trivial                  : 1
% 0.19/0.43  # ...subsumed                          : 601
% 0.19/0.43  # ...remaining for further processing  : 201
% 0.19/0.43  # Other redundant clauses eliminated   : 2
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 18
% 0.19/0.43  # Backward-rewritten                   : 25
% 0.19/0.43  # Generated clauses                    : 2053
% 0.19/0.43  # ...of the previous two non-trivial   : 1858
% 0.19/0.43  # Contextual simplify-reflections      : 24
% 0.19/0.43  # Paramodulations                      : 2051
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 2
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 137
% 0.19/0.43  #    Positive orientable unit clauses  : 11
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 3
% 0.19/0.43  #    Non-unit-clauses                  : 123
% 0.19/0.43  # Current number of unprocessed clauses: 1055
% 0.19/0.43  # ...number of literals in the above   : 5952
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 63
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 8389
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 3566
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 388
% 0.19/0.43  # Unit Clause-clause subsumption calls : 120
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 15
% 0.19/0.43  # BW rewrite match successes           : 1
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 32617
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.084 s
% 0.19/0.43  # System time              : 0.005 s
% 0.19/0.43  # Total time               : 0.090 s
% 0.19/0.43  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
