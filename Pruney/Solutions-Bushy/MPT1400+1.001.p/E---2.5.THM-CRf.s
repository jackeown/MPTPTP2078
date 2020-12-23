%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1400+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:14 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   97 (13474 expanded)
%              Number of clauses        :   76 (5050 expanded)
%              Number of leaves         :   10 (3249 expanded)
%              Depth                    :   21
%              Number of atoms          :  552 (108587 expanded)
%              Number of equality atoms :   84 (15199 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :  103 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k1_connsp_2(X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                    & ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r2_hidden(X5,X4)
                        <=> ( v3_pre_topc(X5,X1)
                            & v4_pre_topc(X5,X1)
                            & r2_hidden(X2,X5) ) ) )
                    & k6_setfam_1(u1_struct_0(X1),X4) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_2)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(t30_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_hidden(X2,k1_connsp_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t28_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r2_hidden(X4,X3)
                      <=> ( v3_pre_topc(X4,X1)
                          & v4_pre_topc(X4,X1)
                          & r2_hidden(X2,X4) ) ) )
                  & X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_10,plain,(
    ! [X19,X20,X21,X23,X24] :
      ( ( m1_subset_1(esk4_3(X19,X20,X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | X21 != k1_connsp_2(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( v3_pre_topc(X23,X19)
        | ~ r2_hidden(X23,esk4_3(X19,X20,X21))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X19)))
        | X21 != k1_connsp_2(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( v4_pre_topc(X23,X19)
        | ~ r2_hidden(X23,esk4_3(X19,X20,X21))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X19)))
        | X21 != k1_connsp_2(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(X20,X23)
        | ~ r2_hidden(X23,esk4_3(X19,X20,X21))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X19)))
        | X21 != k1_connsp_2(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ v3_pre_topc(X23,X19)
        | ~ v4_pre_topc(X23,X19)
        | ~ r2_hidden(X20,X23)
        | r2_hidden(X23,esk4_3(X19,X20,X21))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X19)))
        | X21 != k1_connsp_2(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( k6_setfam_1(u1_struct_0(X19),esk4_3(X19,X20,X21)) = X21
        | X21 != k1_connsp_2(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk5_4(X19,X20,X21,X24),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | k6_setfam_1(u1_struct_0(X19),X24) != X21
        | X21 = k1_connsp_2(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(esk5_4(X19,X20,X21,X24),X24)
        | ~ v3_pre_topc(esk5_4(X19,X20,X21,X24),X19)
        | ~ v4_pre_topc(esk5_4(X19,X20,X21,X24),X19)
        | ~ r2_hidden(X20,esk5_4(X19,X20,X21,X24))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | k6_setfam_1(u1_struct_0(X19),X24) != X21
        | X21 = k1_connsp_2(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( v3_pre_topc(esk5_4(X19,X20,X21,X24),X19)
        | r2_hidden(esk5_4(X19,X20,X21,X24),X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | k6_setfam_1(u1_struct_0(X19),X24) != X21
        | X21 = k1_connsp_2(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( v4_pre_topc(esk5_4(X19,X20,X21,X24),X19)
        | r2_hidden(esk5_4(X19,X20,X21,X24),X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | k6_setfam_1(u1_struct_0(X19),X24) != X21
        | X21 = k1_connsp_2(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(X20,esk5_4(X19,X20,X21,X24))
        | r2_hidden(esk5_4(X19,X20,X21,X24),X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | k6_setfam_1(u1_struct_0(X19),X24) != X21
        | X21 = k1_connsp_2(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_connsp_2])])])])])])).

fof(c_0_11,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | m1_subset_1(k1_connsp_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r2_hidden(X2,k1_connsp_2(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t30_connsp_2])).

cnf(c_0_13,plain,
    ( k6_setfam_1(u1_struct_0(X1),esk4_3(X1,X2,X3)) = X3
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v2_pre_topc(esk7_0)
    & l1_pre_topc(esk7_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk7_0))
    & ~ r2_hidden(esk8_0,k1_connsp_2(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_16,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k1_zfmisc_1(X28)))
      | k6_setfam_1(X28,X29) = k1_setfam_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_17,plain,
    ( k6_setfam_1(u1_struct_0(X1),esk4_3(X1,X2,k1_connsp_2(X1,X2))) = k1_connsp_2(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_23,plain,(
    ! [X6,X7,X8,X9,X10,X12,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X8,X7)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X8,X9)
        | X7 != k1_setfam_1(X6)
        | X6 = k1_xboole_0 )
      & ( r2_hidden(esk1_3(X6,X7,X10),X6)
        | r2_hidden(X10,X7)
        | X7 != k1_setfam_1(X6)
        | X6 = k1_xboole_0 )
      & ( ~ r2_hidden(X10,esk1_3(X6,X7,X10))
        | r2_hidden(X10,X7)
        | X7 != k1_setfam_1(X6)
        | X6 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X6,X12),X6)
        | ~ r2_hidden(esk2_2(X6,X12),X12)
        | X12 = k1_setfam_1(X6)
        | X6 = k1_xboole_0 )
      & ( ~ r2_hidden(esk2_2(X6,X12),esk3_2(X6,X12))
        | ~ r2_hidden(esk2_2(X6,X12),X12)
        | X12 = k1_setfam_1(X6)
        | X6 = k1_xboole_0 )
      & ( r2_hidden(esk2_2(X6,X12),X12)
        | ~ r2_hidden(X15,X6)
        | r2_hidden(esk2_2(X6,X12),X15)
        | X12 = k1_setfam_1(X6)
        | X6 = k1_xboole_0 )
      & ( X17 != k1_setfam_1(X16)
        | X17 = k1_xboole_0
        | X16 != k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | X18 = k1_setfam_1(X16)
        | X16 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_24,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk7_0),esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0))) = k1_connsp_2(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk4_3(X1,X2,k1_connsp_2(X1,X2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_14])).

fof(c_0_27,plain,(
    ! [X38,X39,X40] :
      ( ~ r2_hidden(X38,X39)
      | ~ m1_subset_1(X39,k1_zfmisc_1(X40))
      | m1_subset_1(X38,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k1_setfam_1(esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0))) = k1_connsp_2(esk7_0,esk8_0)
    | ~ m1_subset_1(esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k1_setfam_1(esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0))) = k1_connsp_2(esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk1_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X2,esk4_3(X3,X1,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != k1_connsp_2(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(X1,esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)) = k1_xboole_0
    | r2_hidden(esk1_3(esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)),k1_connsp_2(esk7_0,esk8_0),X1),esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)))
    | r2_hidden(X1,k1_connsp_2(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X3,esk4_3(X1,X2,k1_connsp_2(X1,X2))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)),k1_connsp_2(esk7_0,esk8_0),X1),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | r2_hidden(X1,k1_connsp_2(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)) = k1_xboole_0
    | r2_hidden(X1,k1_connsp_2(esk7_0,esk8_0))
    | ~ r2_hidden(X1,esk1_3(esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)),k1_connsp_2(esk7_0,esk8_0),X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)) = k1_xboole_0
    | r2_hidden(esk8_0,esk1_3(esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)),k1_connsp_2(esk7_0,esk8_0),X1))
    | r2_hidden(X1,k1_connsp_2(esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k1_connsp_2(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,plain,
    ( X1 = k1_setfam_1(X2)
    | X1 != k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,esk4_3(X2,X3,X4))
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k1_connsp_2(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).

fof(c_0_48,plain,(
    ! [X30,X31] :
      ( ~ r2_hidden(X30,X31)
      | m1_subset_1(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,esk4_3(X1,X3,k1_connsp_2(X1,X3)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(k1_connsp_2(X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_45,c_0_31])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k1_connsp_2(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

fof(c_0_51,plain,(
    ! [X32,X33,X34] :
      ( ( m1_subset_1(esk6_3(X32,X33,X34),k1_zfmisc_1(u1_struct_0(X32)))
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ r2_hidden(esk6_3(X32,X33,X34),X34)
        | ~ v3_pre_topc(esk6_3(X32,X33,X34),X32)
        | ~ v4_pre_topc(esk6_3(X32,X33,X34),X32)
        | ~ r2_hidden(X33,esk6_3(X32,X33,X34))
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( v3_pre_topc(esk6_3(X32,X33,X34),X32)
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( v4_pre_topc(esk6_3(X32,X33,X34),X32)
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( r2_hidden(X33,esk6_3(X32,X33,X34))
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_connsp_2])])])])])])).

cnf(c_0_52,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,esk4_3(X2,X3,X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k1_connsp_2(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( k1_connsp_2(esk7_0,esk8_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_46]),c_0_47])).

cnf(c_0_54,plain,
    ( v4_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,esk4_3(X2,X3,X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k1_connsp_2(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)))
    | ~ v4_pre_topc(X1,esk7_0)
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( v3_pre_topc(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ r2_hidden(X1,esk4_3(X2,X3,k1_connsp_2(X2,X3))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_46])).

cnf(c_0_62,plain,
    ( v4_pre_topc(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( v4_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ r2_hidden(X1,esk4_3(X2,X3,k1_connsp_2(X2,X3))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_14])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,esk6_3(X2,X1,X3))
    | r2_hidden(esk6_3(X2,X1,X3),X3)
    | v2_struct_0(X2)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(X1,esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)))
    | ~ v4_pre_topc(X1,esk7_0)
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,plain,
    ( m1_subset_1(esk6_3(X1,X2,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_46])).

cnf(c_0_68,plain,
    ( v3_pre_topc(esk6_3(X1,X2,k1_xboole_0),X1)
    | v2_struct_0(X1)
    | r2_hidden(esk6_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( v3_pre_topc(X1,esk7_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_53]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_60]),c_0_61])).

cnf(c_0_70,plain,
    ( v4_pre_topc(esk6_3(X1,X2,k1_xboole_0),X1)
    | v2_struct_0(X1)
    | r2_hidden(esk6_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( v4_pre_topc(X1,esk7_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_53]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_60]),c_0_61])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk6_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | r2_hidden(X2,esk6_3(X1,X2,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(X1,k1_xboole_0)
    | ~ v4_pre_topc(X1,esk7_0)
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(rw,[status(thm)],[c_0_65,c_0_46])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk6_3(esk7_0,X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_75,negated_conjecture,
    ( v3_pre_topc(esk6_3(esk7_0,X1,k1_xboole_0),esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_67]),c_0_19]),c_0_20])]),c_0_21]),c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( v4_pre_topc(esk6_3(esk7_0,X1,k1_xboole_0),esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_67]),c_0_19]),c_0_20])]),c_0_21]),c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk6_3(esk7_0,X1,k1_xboole_0),k1_xboole_0)
    | r2_hidden(X1,esk6_3(esk7_0,X1,k1_xboole_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_67]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_53]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_60]),c_0_61])).

fof(c_0_79,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,X42)
      | ~ v1_xboole_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_80,plain,
    ( v2_struct_0(X1)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X3)
    | ~ v3_pre_topc(esk6_3(X1,X2,X3),X1)
    | ~ v4_pre_topc(esk6_3(X1,X2,X3),X1)
    | ~ r2_hidden(X2,esk6_3(X1,X2,X3))
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_81,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X36,X37)
      | v1_xboole_0(X37)
      | r2_hidden(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk6_3(esk7_0,X1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(esk8_0,esk6_3(esk7_0,X1,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk8_0,esk6_3(esk7_0,esk8_0,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_18]),c_0_78])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | ~ v4_pre_topc(esk6_3(X1,X2,k1_xboole_0),X1)
    | ~ v3_pre_topc(esk6_3(X1,X2,k1_xboole_0),X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(esk6_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(X2,esk6_3(X1,X2,k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_61])).

cnf(c_0_87,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk6_3(esk7_0,esk8_0,k1_xboole_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_18])])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_xboole_0(esk4_3(esk7_0,esk8_0,k1_connsp_2(esk7_0,esk8_0)))
    | ~ v4_pre_topc(X1,esk7_0)
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_56])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(esk6_3(esk7_0,X1,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(X1,esk6_3(esk7_0,X1,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_67]),c_0_19]),c_0_20])]),c_0_21]),c_0_86]),c_0_69]),c_0_71])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0)
    | r2_hidden(esk6_3(esk7_0,esk8_0,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v4_pre_topc(X1,esk7_0)
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(rw,[status(thm)],[c_0_89,c_0_46])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_83])])).

cnf(c_0_94,negated_conjecture,
    ( ~ v4_pre_topc(X1,esk7_0)
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])])).

cnf(c_0_95,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(esk8_0,esk6_3(esk7_0,X1,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_74]),c_0_75]),c_0_76])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_83]),c_0_18])]),
    [proof]).

%------------------------------------------------------------------------------
