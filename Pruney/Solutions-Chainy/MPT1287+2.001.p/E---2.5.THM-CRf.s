%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:41 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 144 expanded)
%              Number of clauses        :   37 (  63 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  184 ( 462 expanded)
%              Number of equality atoms :   18 (  63 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t101_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_tops_1(X2,X1)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_tops_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t108_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v5_tops_1(X2,X1)
                  & v5_tops_1(X3,X1) )
               => v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t109_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v6_tops_1(X2,X1)
                  & v6_tops_1(X3,X1) )
               => v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tops_1)).

fof(c_0_11,plain,(
    ! [X28,X29] :
      ( ( ~ v6_tops_1(X29,X28)
        | v5_tops_1(k3_subset_1(u1_struct_0(X28),X29),X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X28),X29),X28)
        | v6_tops_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_tops_1])])])])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | k3_subset_1(X15,X16) = k4_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_13,plain,(
    ! [X8,X9,X10] : k4_xboole_0(X8,k3_xboole_0(X9,X10)) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X10)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

fof(c_0_14,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X23))
      | k9_subset_1(X23,X24,X25) = k3_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_16,plain,
    ( v6_tops_1(X2,X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v6_tops_1(X1,X2)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( k9_subset_1(X2,X3,X1) = k4_xboole_0(X3,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

fof(c_0_24,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | m1_subset_1(k9_subset_1(X17,X18,X19),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_25,plain,
    ( v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ v5_tops_1(k2_xboole_0(k4_xboole_0(u1_struct_0(X3),X1),k4_xboole_0(u1_struct_0(X3),X2)),X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k9_subset_1(X2,X3,X4)) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),k9_subset_1(X4,X1,X2)),X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

fof(c_0_30,plain,(
    ! [X30,X31,X32] :
      ( ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ v5_tops_1(X31,X30)
      | ~ v5_tops_1(X32,X30)
      | v5_tops_1(k4_subset_1(u1_struct_0(X30),X31,X32),X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_tops_1])])])).

fof(c_0_31,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | k4_subset_1(X20,X21,X22) = k2_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_32,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_33,plain,(
    ! [X11,X12] : r1_tarski(k4_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_34,plain,
    ( v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),k9_subset_1(X4,X1,X2)),X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_tops_1(X2,X1)
    | ~ v5_tops_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ v5_tops_1(k2_xboole_0(k4_xboole_0(u1_struct_0(X3),X1),k4_xboole_0(u1_struct_0(X3),X2)),X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_40,plain,
    ( v5_tops_1(k2_xboole_0(X1,X2),X3)
    | ~ v2_pre_topc(X3)
    | ~ v5_tops_1(X2,X3)
    | ~ v5_tops_1(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v6_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,plain,
    ( v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ v2_pre_topc(X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),X2),X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),X1),X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_41])])).

cnf(c_0_44,plain,
    ( v5_tops_1(k4_xboole_0(u1_struct_0(X1),X2),X1)
    | ~ v6_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_17])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v6_tops_1(X2,X1)
                    & v6_tops_1(X3,X1) )
                 => v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t109_tops_1])).

cnf(c_0_46,plain,
    ( v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ v2_pre_topc(X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),X1),X3)
    | ~ v6_tops_1(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_47,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v6_tops_1(esk2_0,esk1_0)
    & v6_tops_1(esk3_0,esk1_0)
    & ~ v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

cnf(c_0_48,plain,
    ( v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ v2_pre_topc(X3)
    | ~ v6_tops_1(X2,X3)
    | ~ v6_tops_1(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( ~ v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)),esk1_0)
    | ~ v6_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( v6_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( ~ v6_tops_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_23]),c_0_49])])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])]),c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_49,c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:51:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.41/2.65  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.41/2.65  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.41/2.65  #
% 2.41/2.65  # Preprocessing time       : 0.028 s
% 2.41/2.65  # Presaturation interreduction done
% 2.41/2.65  
% 2.41/2.65  # Proof found!
% 2.41/2.65  # SZS status Theorem
% 2.41/2.65  # SZS output start CNFRefutation
% 2.41/2.65  fof(t101_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_tops_1(X2,X1)<=>v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_tops_1)).
% 2.41/2.65  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.41/2.65  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 2.41/2.65  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.41/2.65  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.41/2.65  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.41/2.65  fof(t108_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v5_tops_1(X2,X1)&v5_tops_1(X3,X1))=>v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tops_1)).
% 2.41/2.65  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.41/2.65  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.41/2.65  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.41/2.65  fof(t109_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v6_tops_1(X2,X1)&v6_tops_1(X3,X1))=>v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tops_1)).
% 2.41/2.65  fof(c_0_11, plain, ![X28, X29]:((~v6_tops_1(X29,X28)|v5_tops_1(k3_subset_1(u1_struct_0(X28),X29),X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(~v5_tops_1(k3_subset_1(u1_struct_0(X28),X29),X28)|v6_tops_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_tops_1])])])])).
% 2.41/2.65  fof(c_0_12, plain, ![X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|k3_subset_1(X15,X16)=k4_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 2.41/2.65  fof(c_0_13, plain, ![X8, X9, X10]:k4_xboole_0(X8,k3_xboole_0(X9,X10))=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X10)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 2.41/2.65  fof(c_0_14, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.41/2.65  fof(c_0_15, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(X23))|k9_subset_1(X23,X24,X25)=k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 2.41/2.65  cnf(c_0_16, plain, (v6_tops_1(X2,X1)|~v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.41/2.65  cnf(c_0_17, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.41/2.65  cnf(c_0_18, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.41/2.65  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.41/2.65  cnf(c_0_20, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.41/2.65  cnf(c_0_21, plain, (v6_tops_1(X1,X2)|~v5_tops_1(k4_xboole_0(u1_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 2.41/2.65  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 2.41/2.65  cnf(c_0_23, plain, (k9_subset_1(X2,X3,X1)=k4_xboole_0(X3,k4_xboole_0(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 2.41/2.65  fof(c_0_24, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X17))|m1_subset_1(k9_subset_1(X17,X18,X19),k1_zfmisc_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 2.41/2.65  cnf(c_0_25, plain, (v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~v5_tops_1(k2_xboole_0(k4_xboole_0(u1_struct_0(X3),X1),k4_xboole_0(u1_struct_0(X3),X2)),X3)|~l1_pre_topc(X3)|~m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 2.41/2.65  cnf(c_0_26, plain, (k4_xboole_0(X1,k9_subset_1(X2,X3,X4))=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X4))|~m1_subset_1(X4,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 2.41/2.65  cnf(c_0_27, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.41/2.65  cnf(c_0_28, plain, (v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~v5_tops_1(k4_xboole_0(u1_struct_0(X3),k9_subset_1(X4,X1,X2)),X3)|~l1_pre_topc(X3)|~m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 2.41/2.65  cnf(c_0_29, plain, (m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_27, c_0_23])).
% 2.41/2.65  fof(c_0_30, plain, ![X30, X31, X32]:(~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|(~v5_tops_1(X31,X30)|~v5_tops_1(X32,X30)|v5_tops_1(k4_subset_1(u1_struct_0(X30),X31,X32),X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_tops_1])])])).
% 2.41/2.65  fof(c_0_31, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|~m1_subset_1(X22,k1_zfmisc_1(X20))|k4_subset_1(X20,X21,X22)=k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 2.41/2.65  fof(c_0_32, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.41/2.65  fof(c_0_33, plain, ![X11, X12]:r1_tarski(k4_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 2.41/2.65  cnf(c_0_34, plain, (v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~v5_tops_1(k4_xboole_0(u1_struct_0(X3),k9_subset_1(X4,X1,X2)),X3)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 2.41/2.65  cnf(c_0_35, plain, (v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v5_tops_1(X2,X1)|~v5_tops_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.41/2.65  cnf(c_0_36, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.41/2.65  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.41/2.65  cnf(c_0_38, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.41/2.65  cnf(c_0_39, plain, (v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~v5_tops_1(k2_xboole_0(k4_xboole_0(u1_struct_0(X3),X1),k4_xboole_0(u1_struct_0(X3),X2)),X3)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 2.41/2.65  cnf(c_0_40, plain, (v5_tops_1(k2_xboole_0(X1,X2),X3)|~v2_pre_topc(X3)|~v5_tops_1(X2,X3)|~v5_tops_1(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 2.41/2.65  cnf(c_0_41, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.41/2.65  cnf(c_0_42, plain, (v5_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v6_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.41/2.65  cnf(c_0_43, plain, (v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~v2_pre_topc(X3)|~v5_tops_1(k4_xboole_0(u1_struct_0(X3),X2),X3)|~v5_tops_1(k4_xboole_0(u1_struct_0(X3),X1),X3)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_41])])).
% 2.41/2.65  cnf(c_0_44, plain, (v5_tops_1(k4_xboole_0(u1_struct_0(X1),X2),X1)|~v6_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_42, c_0_17])).
% 2.41/2.65  fof(c_0_45, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v6_tops_1(X2,X1)&v6_tops_1(X3,X1))=>v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t109_tops_1])).
% 2.41/2.65  cnf(c_0_46, plain, (v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~v2_pre_topc(X3)|~v5_tops_1(k4_xboole_0(u1_struct_0(X3),X1),X3)|~v6_tops_1(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 2.41/2.65  fof(c_0_47, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((v6_tops_1(esk2_0,esk1_0)&v6_tops_1(esk3_0,esk1_0))&~v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).
% 2.41/2.65  cnf(c_0_48, plain, (v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~v2_pre_topc(X3)|~v6_tops_1(X2,X3)|~v6_tops_1(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_46, c_0_44])).
% 2.41/2.65  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.41/2.65  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.41/2.65  cnf(c_0_51, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.41/2.65  cnf(c_0_52, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.41/2.65  cnf(c_0_53, negated_conjecture, (~v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.41/2.65  cnf(c_0_54, negated_conjecture, (v6_tops_1(k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)),esk1_0)|~v6_tops_1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_52])])).
% 2.41/2.65  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.41/2.65  cnf(c_0_56, negated_conjecture, (v6_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.41/2.65  cnf(c_0_57, negated_conjecture, (~v6_tops_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_23]), c_0_49])])).
% 2.41/2.65  cnf(c_0_58, negated_conjecture, (~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])]), c_0_57])).
% 2.41/2.65  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_49, c_0_58]), ['proof']).
% 2.41/2.65  # SZS output end CNFRefutation
% 2.41/2.65  # Proof object total steps             : 60
% 2.41/2.65  # Proof object clause steps            : 37
% 2.41/2.65  # Proof object formula steps           : 23
% 2.41/2.65  # Proof object conjectures             : 14
% 2.41/2.65  # Proof object clause conjectures      : 11
% 2.41/2.65  # Proof object formula conjectures     : 3
% 2.41/2.65  # Proof object initial clauses used    : 18
% 2.41/2.65  # Proof object initial formulas used   : 11
% 2.41/2.65  # Proof object generating inferences   : 16
% 2.41/2.65  # Proof object simplifying inferences  : 15
% 2.41/2.65  # Training examples: 0 positive, 0 negative
% 2.41/2.65  # Parsed axioms                        : 13
% 2.41/2.65  # Removed by relevancy pruning/SinE    : 0
% 2.41/2.65  # Initial clauses                      : 23
% 2.41/2.65  # Removed in clause preprocessing      : 1
% 2.41/2.65  # Initial clauses in saturation        : 22
% 2.41/2.65  # Processed clauses                    : 2826
% 2.41/2.65  # ...of these trivial                  : 218
% 2.41/2.65  # ...subsumed                          : 1577
% 2.41/2.65  # ...remaining for further processing  : 1031
% 2.41/2.65  # Other redundant clauses eliminated   : 2
% 2.41/2.65  # Clauses deleted for lack of memory   : 0
% 2.41/2.65  # Backward-subsumed                    : 141
% 2.41/2.65  # Backward-rewritten                   : 126
% 2.41/2.65  # Generated clauses                    : 203297
% 2.41/2.65  # ...of the previous two non-trivial   : 200254
% 2.41/2.65  # Contextual simplify-reflections      : 2
% 2.41/2.65  # Paramodulations                      : 203294
% 2.41/2.65  # Factorizations                       : 0
% 2.41/2.65  # Equation resolutions                 : 2
% 2.41/2.65  # Propositional unsat checks           : 0
% 2.41/2.65  #    Propositional check models        : 0
% 2.41/2.65  #    Propositional check unsatisfiable : 0
% 2.41/2.65  #    Propositional clauses             : 0
% 2.41/2.65  #    Propositional clauses after purity: 0
% 2.41/2.65  #    Propositional unsat core size     : 0
% 2.41/2.65  #    Propositional preprocessing time  : 0.000
% 2.41/2.65  #    Propositional encoding time       : 0.000
% 2.41/2.65  #    Propositional solver time         : 0.000
% 2.41/2.65  #    Success case prop preproc time    : 0.000
% 2.41/2.65  #    Success case prop encoding time   : 0.000
% 2.41/2.65  #    Success case prop solver time     : 0.000
% 2.41/2.65  # Current number of processed clauses  : 740
% 2.41/2.65  #    Positive orientable unit clauses  : 120
% 2.41/2.65  #    Positive unorientable unit clauses: 72
% 2.41/2.65  #    Negative unit clauses             : 3
% 2.41/2.65  #    Non-unit-clauses                  : 545
% 2.41/2.65  # Current number of unprocessed clauses: 197067
% 2.41/2.65  # ...number of literals in the above   : 423912
% 2.41/2.65  # Current number of archived formulas  : 0
% 2.41/2.65  # Current number of archived clauses   : 290
% 2.41/2.65  # Clause-clause subsumption calls (NU) : 120089
% 2.41/2.65  # Rec. Clause-clause subsumption calls : 90196
% 2.41/2.65  # Non-unit clause-clause subsumptions  : 1692
% 2.41/2.65  # Unit Clause-clause subsumption calls : 3489
% 2.41/2.65  # Rewrite failures with RHS unbound    : 0
% 2.41/2.65  # BW rewrite match attempts            : 4423
% 2.41/2.65  # BW rewrite match successes           : 427
% 2.41/2.65  # Condensation attempts                : 0
% 2.41/2.65  # Condensation successes               : 0
% 2.41/2.65  # Termbank termtop insertions          : 6198098
% 2.41/2.66  
% 2.41/2.66  # -------------------------------------------------
% 2.41/2.66  # User time                : 2.234 s
% 2.41/2.66  # System time              : 0.091 s
% 2.41/2.66  # Total time               : 2.325 s
% 2.41/2.66  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
