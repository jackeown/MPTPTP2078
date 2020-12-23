%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_1__t86_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:33 EDT 2019

% Result     : Theorem 1.06s
% Output     : CNFRefutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 910 expanded)
%              Number of clauses        :   41 ( 337 expanded)
%              Number of leaves         :    6 ( 220 expanded)
%              Depth                    :   14
%              Number of atoms          :  202 (6406 expanded)
%              Number of equality atoms :   14 ( 652 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/tops_1__t86_tops_1.p',t86_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t86_tops_1.p',dt_k3_subset_1)).

fof(t80_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( X3 != k1_xboole_0
                    & v3_pre_topc(X3,X1)
                    & r1_xboole_0(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t86_tops_1.p',t80_tops_1)).

fof(d4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t86_tops_1.p',d4_tops_1)).

fof(t44_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t86_tops_1.p',t44_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t86_tops_1.p',symmetry_r1_xboole_0)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | m1_subset_1(k3_subset_1(X12,X13),k1_zfmisc_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_8,negated_conjecture,(
    ! [X7] :
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
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r1_tarski(X7,esk2_0)
        | ~ v3_pre_topc(X7,esk1_0)
        | X7 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X43,X44,X45] :
      ( ( ~ v1_tops_1(X44,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X43)))
        | X45 = k1_xboole_0
        | ~ v3_pre_topc(X45,X43)
        | ~ r1_xboole_0(X44,X45)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( m1_subset_1(esk7_2(X43,X44),k1_zfmisc_1(u1_struct_0(X43)))
        | v1_tops_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( esk7_2(X43,X44) != k1_xboole_0
        | v1_tops_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( v3_pre_topc(esk7_2(X43,X44),X43)
        | v1_tops_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( r1_xboole_0(X44,esk7_2(X43,X44))
        | v1_tops_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_tops_1])])])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X10,X11] :
      ( ( ~ v2_tops_1(X11,X10)
        | v1_tops_1(k3_subset_1(u1_struct_0(X10),X11),X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X10),X11),X10)
        | v2_tops_1(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).

fof(c_0_13,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r1_xboole_0(X31,k3_subset_1(X30,X32))
        | r1_tarski(X31,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(X30)) )
      & ( ~ r1_tarski(X31,X32)
        | r1_xboole_0(X31,k3_subset_1(X30,X32))
        | ~ m1_subset_1(X32,k1_zfmisc_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_subset_1])])])])).

fof(c_0_14,plain,(
    ! [X21,X22] :
      ( ~ r1_xboole_0(X21,X22)
      | r1_xboole_0(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,esk7_2(X2,X1))
    | v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk7_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( v3_pre_topc(esk7_2(X1,X2),X1)
    | v1_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk7_2(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_25,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0)
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0)
    | ~ v3_pre_topc(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | m1_subset_1(esk7_2(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_27,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | v3_pre_topc(esk7_2(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_28,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_11]),c_0_17])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(esk7_2(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( esk7_2(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k1_xboole_0
    | v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ r1_tarski(esk7_2(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | r1_tarski(esk7_2(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_30])).

cnf(c_0_33,plain,
    ( v2_tops_1(X2,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,plain,
    ( v1_tops_1(X2,X1)
    | esk7_2(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( esk7_2(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k1_xboole_0
    | v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_11]),c_0_17])])).

cnf(c_0_37,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k3_subset_1(X3,X2))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_40,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0)
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_43,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ r1_tarski(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_40])])).

cnf(c_0_47,plain,
    ( X3 = k1_xboole_0
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X3,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_40])])).

cnf(c_0_49,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_40])])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_xboole_0(X1,esk3_0)
    | ~ v1_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_48]),c_0_17]),c_0_18])]),c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_16]),c_0_52]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
