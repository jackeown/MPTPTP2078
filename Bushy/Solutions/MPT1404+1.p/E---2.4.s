%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : connsp_2__t34_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:53 EDT 2019

% Result     : Theorem 41.01s
% Output     : CNFRefutation 41.01s
% Verified   : 
% Statistics : Number of formulae       :  141 (258525 expanded)
%              Number of clauses        :  106 (101307 expanded)
%              Number of leaves         :   17 (63174 expanded)
%              Depth                    :   40
%              Number of atoms          :  530 (1655951 expanded)
%              Number of equality atoms :   33 (64633 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal clause size      :   76 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ! [X4] :
                    ( m1_connsp_2(X4,X1,X3)
                   => ~ r1_xboole_0(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t34_connsp_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t2_subset)).

fof(d13_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k2_pre_topc(X1,X2)
              <=> ! [X4] :
                    ( r2_hidden(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v3_pre_topc(X5,X1)
                              & r2_hidden(X4,X5)
                              & r1_xboole_0(X2,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',d13_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',dt_k2_pre_topc)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',dt_l1_pre_topc)).

fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t5_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t4_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t1_subset)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',symmetry_r1_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t6_boole)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',dt_m1_connsp_2)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t44_tops_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',t63_xboole_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',dt_k1_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',fc9_tops_1)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t34_connsp_2.p',d1_connsp_2)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k2_pre_topc(X1,X2))
                <=> ! [X4] :
                      ( m1_connsp_2(X4,X1,X3)
                     => ~ r1_xboole_0(X4,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_connsp_2])).

fof(c_0_18,plain,(
    ! [X48,X49] :
      ( ~ m1_subset_1(X48,X49)
      | v1_xboole_0(X49)
      | r2_hidden(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_19,negated_conjecture,(
    ! [X10] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
      & ( m1_connsp_2(esk4_0,esk1_0,esk3_0)
        | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) )
      & ( r1_xboole_0(esk4_0,esk2_0)
        | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) )
      & ( r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0))
        | ~ m1_connsp_2(X10,esk1_0,esk3_0)
        | ~ r1_xboole_0(X10,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])])).

fof(c_0_20,plain,(
    ! [X13,X14,X15,X16,X17,X21] :
      ( ( ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v3_pre_topc(X17,X13)
        | ~ r2_hidden(X16,X17)
        | ~ r1_xboole_0(X14,X17)
        | ~ r2_hidden(X16,u1_struct_0(X13))
        | X15 != k2_pre_topc(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk5_4(X13,X14,X15,X16),k1_zfmisc_1(u1_struct_0(X13)))
        | r2_hidden(X16,X15)
        | ~ r2_hidden(X16,u1_struct_0(X13))
        | X15 != k2_pre_topc(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( v3_pre_topc(esk5_4(X13,X14,X15,X16),X13)
        | r2_hidden(X16,X15)
        | ~ r2_hidden(X16,u1_struct_0(X13))
        | X15 != k2_pre_topc(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(X16,esk5_4(X13,X14,X15,X16))
        | r2_hidden(X16,X15)
        | ~ r2_hidden(X16,u1_struct_0(X13))
        | X15 != k2_pre_topc(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( r1_xboole_0(X14,esk5_4(X13,X14,X15,X16))
        | r2_hidden(X16,X15)
        | ~ r2_hidden(X16,u1_struct_0(X13))
        | X15 != k2_pre_topc(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk6_3(X13,X14,X15),u1_struct_0(X13))
        | X15 = k2_pre_topc(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk7_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(esk6_3(X13,X14,X15),X15)
        | X15 = k2_pre_topc(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( v3_pre_topc(esk7_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk6_3(X13,X14,X15),X15)
        | X15 = k2_pre_topc(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk6_3(X13,X14,X15),esk7_3(X13,X14,X15))
        | ~ r2_hidden(esk6_3(X13,X14,X15),X15)
        | X15 = k2_pre_topc(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( r1_xboole_0(X14,esk7_3(X13,X14,X15))
        | ~ r2_hidden(esk6_3(X13,X14,X15),X15)
        | X15 = k2_pre_topc(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk6_3(X13,X14,X15),X15)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v3_pre_topc(X21,X13)
        | ~ r2_hidden(esk6_3(X13,X14,X15),X21)
        | ~ r1_xboole_0(X14,X21)
        | X15 = k2_pre_topc(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).

fof(c_0_21,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | m1_subset_1(k2_pre_topc(X27,X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_22,plain,(
    ! [X71] :
      ( v2_struct_0(X71)
      | ~ l1_struct_0(X71)
      | ~ v1_xboole_0(u1_struct_0(X71)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk5_4(X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_pre_topc(X2,X3))
    | m1_subset_1(esk5_4(X2,X3,k2_pre_topc(X2,X3),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X57,X58,X59] :
      ( v2_struct_0(X57)
      | ~ v2_pre_topc(X57)
      | ~ l1_pre_topc(X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
      | ~ m1_subset_1(X59,u1_struct_0(X57))
      | ~ v3_pre_topc(X58,X57)
      | ~ r2_hidden(X59,X58)
      | m1_connsp_2(X58,X57,X59) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_37,plain,(
    ! [X54,X55,X56] :
      ( ~ r2_hidden(X54,X55)
      | ~ m1_subset_1(X55,k1_zfmisc_1(X56))
      | m1_subset_1(X54,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_38,plain,(
    ! [X46,X47] :
      ( ~ r2_hidden(X46,X47)
      | m1_subset_1(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk1_0,esk2_0))
    | m1_subset_1(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_33])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,esk5_4(X2,X3,X4,X1))
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | X4 != k2_pre_topc(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,plain,
    ( v3_pre_topc(esk5_4(X1,X2,X3,X4),X1)
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,esk5_4(X2,X1,X3,X4))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X2))
    | X3 != k2_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0))
    | m1_subset_1(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,esk5_4(X2,X3,k2_pre_topc(X2,X3),X1))
    | r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_26])).

cnf(c_0_49,plain,
    ( v3_pre_topc(esk5_4(X1,X2,k2_pre_topc(X1,X2),X3),X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_42]),c_0_26])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,esk5_4(X2,X1,k2_pre_topc(X2,X1),X3))
    | r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ r2_hidden(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_26])).

cnf(c_0_51,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),X1))
    | r2_hidden(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_32]),c_0_33])])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),X1),esk1_0)
    | r2_hidden(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_32]),c_0_33])])).

fof(c_0_56,plain,(
    ! [X44,X45] :
      ( ~ r1_xboole_0(X44,X45)
      | r1_xboole_0(X45,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),X1))
    | r2_hidden(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32]),c_0_33])])).

cnf(c_0_58,negated_conjecture,
    ( m1_connsp_2(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),esk1_0,X1)
    | m1_subset_1(esk3_0,k2_pre_topc(esk1_0,esk2_0))
    | ~ v3_pre_topc(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),esk1_0)
    | ~ r2_hidden(X1,esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_33]),c_0_53])]),c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0))
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( v3_pre_topc(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),esk1_0)
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_40])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0))
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0))
    | ~ m1_connsp_2(X1,esk1_0,esk3_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_64,negated_conjecture,
    ( m1_connsp_2(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),esk1_0,esk3_0)
    | m1_subset_1(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_46])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),esk2_0)
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_66,plain,(
    ! [X66] :
      ( ~ v1_xboole_0(X66)
      | X66 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_46])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(k2_pre_topc(esk1_0,esk2_0))
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_67])).

fof(c_0_70,plain,(
    ! [X30,X31,X32] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | ~ m1_connsp_2(X32,X30,X31)
      | m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_71,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk1_0,esk3_0)
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_72,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_73,plain,(
    ! [X52,X53] :
      ( ~ l1_pre_topc(X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
      | r1_tarski(k1_tops_1(X52,X53),X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | m1_connsp_2(esk4_0,esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

fof(c_0_76,plain,(
    ! [X63,X64,X65] :
      ( ~ r1_tarski(X63,X64)
      | ~ r1_xboole_0(X64,X65)
      | r1_xboole_0(X63,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_24]),c_0_33]),c_0_53])]),c_0_29])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | r1_tarski(k1_tops_1(esk1_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_33])])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0)
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_82,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v3_pre_topc(X3,X4)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X5,X3)
    | ~ r2_hidden(X1,u1_struct_0(X4))
    | X2 != k2_pre_topc(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_83,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | m1_subset_1(k1_tops_1(X25,X26),k1_zfmisc_1(u1_struct_0(X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_84,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | r1_xboole_0(k1_tops_1(esk1_0,esk4_0),X1)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | r1_xboole_0(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_72])).

fof(c_0_86,plain,(
    ! [X72,X73] :
      ( ~ v2_pre_topc(X72)
      | ~ l1_pre_topc(X72)
      | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))
      | v3_pre_topc(k1_tops_1(X72,X73),X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_87,plain,(
    ! [X22,X23,X24] :
      ( ( ~ m1_connsp_2(X24,X22,X23)
        | r2_hidden(X23,k1_tops_1(X22,X24))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ r2_hidden(X23,k1_tops_1(X22,X24))
        | m1_connsp_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_88,plain,
    ( ~ v3_pre_topc(X1,X2)
    | ~ r1_xboole_0(X3,X1)
    | ~ r2_hidden(X4,k2_pre_topc(X2,X3))
    | ~ r2_hidden(X4,u1_struct_0(X2))
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_82]),c_0_26])).

cnf(c_0_89,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | r1_xboole_0(k1_tops_1(esk1_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_91,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_92,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk1_0,esk3_0)
    | m1_subset_1(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_47])).

cnf(c_0_94,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_xboole_0(esk2_0,X1)
    | ~ r2_hidden(X2,k2_pre_topc(esk1_0,esk2_0))
    | ~ r2_hidden(X2,u1_struct_0(esk1_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_32]),c_0_33])])).

cnf(c_0_95,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | m1_subset_1(k1_tops_1(esk1_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_78]),c_0_33])])).

cnf(c_0_96,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | r1_xboole_0(esk2_0,k1_tops_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | v3_pre_topc(k1_tops_1(esk1_0,esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_78]),c_0_33]),c_0_53])])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,k1_tops_1(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_92,c_0_74])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_93]),c_0_24]),c_0_33]),c_0_53])]),c_0_29])).

cnf(c_0_100,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | ~ r2_hidden(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0
    | r2_hidden(esk3_0,k1_tops_1(esk1_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_75]),c_0_24]),c_0_33]),c_0_53])]),c_0_29])).

cnf(c_0_102,negated_conjecture,
    ( m1_connsp_2(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),esk1_0,X1)
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),esk1_0)
    | ~ r2_hidden(X1,esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_99]),c_0_33]),c_0_53])]),c_0_29])).

cnf(c_0_103,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_40]),c_0_101]),c_0_72])).

cnf(c_0_104,negated_conjecture,
    ( m1_connsp_2(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),esk1_0,X1)
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),esk1_0)
    | ~ r2_hidden(X1,esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_103]),c_0_103])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0))
    | r2_hidden(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_103]),c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( v3_pre_topc(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),esk1_0)
    | r2_hidden(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_103]),c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk3_0,k1_xboole_0)
    | ~ r1_xboole_0(X1,esk2_0)
    | ~ m1_connsp_2(X1,esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( m1_connsp_2(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),esk1_0,esk3_0)
    | r2_hidden(esk3_0,k1_xboole_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( r1_xboole_0(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),esk2_0)
    | r2_hidden(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_103]),c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk1_0,esk3_0)
    | ~ r2_hidden(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_103])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk3_0,k1_xboole_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk1_0,esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_112]),c_0_24]),c_0_33]),c_0_53])]),c_0_29])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_113]),c_0_33])])).

cnf(c_0_115,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0)
    | m1_subset_1(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_47])).

cnf(c_0_116,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk1_0,esk4_0),X1)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_114])).

cnf(c_0_117,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0)
    | m1_subset_1(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_115,c_0_103])).

cnf(c_0_118,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_xboole_0(esk2_0,X1)
    | ~ r2_hidden(X2,u1_struct_0(esk1_0))
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_94,c_0_103])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_113]),c_0_33])])).

cnf(c_0_120,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_113]),c_0_33]),c_0_53])])).

cnf(c_0_121,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk1_0,esk4_0),esk2_0)
    | m1_subset_1(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_122,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k1_tops_1(esk1_0,esk4_0))
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120])])).

cnf(c_0_123,negated_conjecture,
    ( r1_xboole_0(esk2_0,k1_tops_1(esk1_0,esk4_0))
    | m1_subset_1(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_121])).

cnf(c_0_124,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk1_0,esk3_0)
    | m1_subset_1(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_93,c_0_103])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk1_0,esk4_0))
    | m1_subset_1(esk5_4(esk1_0,esk2_0,k2_pre_topc(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_93]),c_0_24]),c_0_33]),c_0_53])]),c_0_29])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk3_0,k1_xboole_0)
    | m1_subset_1(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_124]),c_0_117])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk1_0,esk4_0))
    | m1_subset_1(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_125,c_0_103])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_40])]),c_0_128])).

cnf(c_0_130,negated_conjecture,
    ( m1_connsp_2(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),esk1_0,X1)
    | ~ v3_pre_topc(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),esk1_0)
    | ~ r2_hidden(X1,esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_129]),c_0_33]),c_0_53])]),c_0_29])).

cnf(c_0_131,negated_conjecture,
    ( m1_connsp_2(esk5_4(esk1_0,esk2_0,k1_xboole_0,esk3_0),esk1_0,esk3_0)
    | r2_hidden(esk3_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_105]),c_0_106])).

cnf(c_0_132,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0)
    | ~ r2_hidden(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_103])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk3_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_131]),c_0_109])).

cnf(c_0_134,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_133])])).

cnf(c_0_135,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk1_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_134])).

cnf(c_0_136,negated_conjecture,
    ( r1_xboole_0(esk2_0,k1_tops_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_135])).

cnf(c_0_137,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_133])])).

cnf(c_0_138,negated_conjecture,
    ( ~ r2_hidden(X1,k1_tops_1(esk1_0,esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_136])])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk1_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_137]),c_0_24]),c_0_33]),c_0_53])]),c_0_29])).

cnf(c_0_140,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_133]),c_0_139]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
