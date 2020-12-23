%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1287+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:03 EST 2020

% Result     : Theorem 11.44s
% Output     : CNFRefutation 11.44s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 180 expanded)
%              Number of clauses        :   41 (  77 expanded)
%              Number of leaves         :   10 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  212 ( 612 expanded)
%              Number of equality atoms :   17 (  77 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

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

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

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

fof(c_0_10,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_11,plain,(
    ! [X24,X25,X26] : k4_xboole_0(X24,k3_xboole_0(X25,X26)) = k2_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,X26)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

fof(c_0_12,plain,(
    ! [X19,X20] :
      ( ( ~ v6_tops_1(X20,X19)
        | v5_tops_1(k3_subset_1(u1_struct_0(X19),X20),X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X19),X20),X19)
        | v6_tops_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_tops_1])])])])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | k3_subset_1(X6,X7) = k4_xboole_0(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | k9_subset_1(X16,X17,X18) = k3_xboole_0(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_17,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v6_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k4_xboole_0(X1,k3_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_15])).

cnf(c_0_20,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X21,X22,X23] :
      ( ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ v5_tops_1(X22,X21)
      | ~ v5_tops_1(X23,X21)
      | v5_tops_1(k4_subset_1(u1_struct_0(X21),X22,X23),X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_tops_1])])])).

fof(c_0_22,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | k4_subset_1(X13,X14,X15) = k2_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_23,plain,
    ( v5_tops_1(k4_xboole_0(u1_struct_0(X1),X2),X1)
    | ~ v6_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k4_xboole_0(X1,k9_subset_1(X4,X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | m1_subset_1(k9_subset_1(X10,X11,X12),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_26,plain,
    ( v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_tops_1(X2,X1)
    | ~ v5_tops_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( v6_tops_1(X2,X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( v5_tops_1(k4_xboole_0(u1_struct_0(X1),k3_xboole_0(X2,X3)),X1)
    | ~ v6_tops_1(k9_subset_1(X4,X3,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k9_subset_1(X4,X3,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( v5_tops_1(k2_xboole_0(X1,X2),X3)
    | ~ v2_pre_topc(X3)
    | ~ v5_tops_1(X2,X3)
    | ~ v5_tops_1(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_32,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | m1_subset_1(k3_subset_1(X8,X9),k1_zfmisc_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_33,negated_conjecture,(
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

cnf(c_0_34,plain,
    ( v6_tops_1(X1,X2)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_35,plain,
    ( v5_tops_1(k4_xboole_0(u1_struct_0(X1),k3_xboole_0(X2,X3)),X1)
    | ~ v6_tops_1(k9_subset_1(u1_struct_0(X1),X3,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( v5_tops_1(k4_xboole_0(X1,k3_xboole_0(X2,X3)),X4)
    | ~ v2_pre_topc(X4)
    | ~ v5_tops_1(k4_xboole_0(X1,X3),X4)
    | ~ v5_tops_1(k4_xboole_0(X1,X2),X4)
    | ~ l1_pre_topc(X4)
    | ~ m1_subset_1(k4_xboole_0(X1,X3),k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(X4))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_15])).

cnf(c_0_37,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v6_tops_1(esk2_0,esk1_0)
    & v6_tops_1(esk3_0,esk1_0)
    & ~ v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_39,plain,
    ( v6_tops_1(k9_subset_1(X1,X2,X3),X4)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X4),k3_xboole_0(X3,X2)),X4)
    | ~ l1_pre_topc(X4)
    | ~ m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_40,plain,
    ( v5_tops_1(k4_xboole_0(u1_struct_0(X1),k3_xboole_0(X2,X3)),X1)
    | ~ v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_19])).

cnf(c_0_41,plain,
    ( v6_tops_1(k3_xboole_0(X1,X2),X3)
    | ~ v2_pre_topc(X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),X2),X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),X1),X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(X3),X2),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(X3),X1),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_42,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_18])).

cnf(c_0_43,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( ~ v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( v6_tops_1(k9_subset_1(X1,X2,X3),X4)
    | ~ v6_tops_1(k9_subset_1(u1_struct_0(X4),X3,X2),X4)
    | ~ l1_pre_topc(X4)
    | ~ m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( v6_tops_1(k3_xboole_0(X1,X2),X3)
    | ~ v2_pre_topc(X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),X2),X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),X1),X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(X3),X1),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( ~ v6_tops_1(k3_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_20]),c_0_45])])).

cnf(c_0_49,plain,
    ( v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v6_tops_1(k9_subset_1(u1_struct_0(X1),X3,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_30])).

cnf(c_0_50,plain,
    ( v6_tops_1(k3_xboole_0(X1,X2),X3)
    | ~ v2_pre_topc(X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),X2),X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),X1),X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( ~ v6_tops_1(k9_subset_1(X1,esk2_0,esk3_0),esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_20])).

cnf(c_0_52,plain,
    ( v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v6_tops_1(k3_xboole_0(X3,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,plain,
    ( v6_tops_1(k3_xboole_0(X1,X2),X3)
    | ~ v2_pre_topc(X3)
    | ~ v5_tops_1(k4_xboole_0(u1_struct_0(X3),X1),X3)
    | ~ v6_tops_1(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( ~ v6_tops_1(k3_xboole_0(esk3_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_45]),c_0_53]),c_0_54])])).

cnf(c_0_57,plain,
    ( v6_tops_1(k3_xboole_0(X1,X2),X3)
    | ~ v2_pre_topc(X3)
    | ~ v6_tops_1(X2,X3)
    | ~ v6_tops_1(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( v6_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_53]),c_0_54]),c_0_45])]),
    [proof]).

%------------------------------------------------------------------------------
