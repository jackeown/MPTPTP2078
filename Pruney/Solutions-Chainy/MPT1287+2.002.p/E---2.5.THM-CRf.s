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
% DateTime   : Thu Dec  3 11:12:42 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 184 expanded)
%              Number of clauses        :   35 (  73 expanded)
%              Number of leaves         :    8 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  179 ( 631 expanded)
%              Number of equality atoms :   16 (  61 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(t101_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_tops_1(X2,X1)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_tops_1)).

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

fof(c_0_8,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | k3_subset_1(X14,k7_subset_1(X14,X15,X16)) = k4_subset_1(X14,k3_subset_1(X14,X15),X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k3_subset_1(X9,k3_subset_1(X9,X10)) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | m1_subset_1(k3_subset_1(X4,X5),k1_zfmisc_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_11,plain,
    ( k3_subset_1(X2,k7_subset_1(X2,X1,X3)) = k4_subset_1(X2,k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k3_subset_1(X1,k7_subset_1(X1,k3_subset_1(X1,X2),X3)) = k4_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

fof(c_0_15,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | m1_subset_1(k7_subset_1(X6,X7,X8),k1_zfmisc_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

cnf(c_0_16,plain,
    ( k3_subset_1(X1,k4_subset_1(X1,X2,X3)) = k7_subset_1(X1,k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(k7_subset_1(X1,k3_subset_1(X1,X2),X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14])).

cnf(c_0_17,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( k3_subset_1(X1,k4_subset_1(X1,X2,X3)) = k7_subset_1(X1,k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_13])).

fof(c_0_19,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ m1_subset_1(X13,k1_zfmisc_1(X11))
      | k7_subset_1(X11,X12,X13) = k9_subset_1(X11,X12,k3_subset_1(X11,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k7_subset_1(X1,k3_subset_1(X1,X2),X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_21,plain,(
    ! [X17,X18] :
      ( ( ~ v6_tops_1(X18,X17)
        | v5_tops_1(k3_subset_1(u1_struct_0(X17),X18),X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X17),X18),X17)
        | v6_tops_1(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_tops_1])])])])).

cnf(c_0_22,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)),X3) = k3_subset_1(X1,k3_subset_1(X1,k7_subset_1(X1,X2,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_11]),c_0_13])).

cnf(c_0_23,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_13])).

cnf(c_0_25,plain,
    ( v6_tops_1(X2,X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k7_subset_1(X1,X2,X3))) = k7_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_12])).

cnf(c_0_27,plain,
    ( k7_subset_1(X1,X2,k3_subset_1(X1,X3)) = k9_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_12]),c_0_13])).

cnf(c_0_28,plain,
    ( m1_subset_1(k3_subset_1(X1,k7_subset_1(X1,X2,X3)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_11]),c_0_13])).

cnf(c_0_29,plain,
    ( v6_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v5_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_12]),c_0_13])).

cnf(c_0_30,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k9_subset_1(X1,X2,X3))) = k9_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_13])).

cnf(c_0_31,plain,
    ( m1_subset_1(k3_subset_1(X1,k9_subset_1(X1,X2,X3)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_13])).

fof(c_0_32,plain,(
    ! [X19,X20,X21] :
      ( ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ v5_tops_1(X20,X19)
      | ~ v5_tops_1(X21,X19)
      | v5_tops_1(k4_subset_1(u1_struct_0(X19),X20,X21),X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_tops_1])])])).

cnf(c_0_33,plain,
    ( v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),k9_subset_1(u1_struct_0(X1),X2,X3)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_34,plain,
    ( v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_tops_1(X2,X1)
    | ~ v5_tops_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_35,negated_conjecture,(
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

cnf(c_0_36,plain,
    ( v6_tops_1(k7_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),k7_subset_1(u1_struct_0(X1),X2,X3)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_13])).

cnf(c_0_37,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X1),k7_subset_1(u1_struct_0(X1),X2,X3)),X1)
    | ~ v2_pre_topc(X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v5_tops_1(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_11]),c_0_13])).

fof(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v6_tops_1(esk2_0,esk1_0)
    & v6_tops_1(esk3_0,esk1_0)
    & ~ v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).

cnf(c_0_39,plain,
    ( v6_tops_1(k7_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v5_tops_1(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( ~ v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_41,plain,
    ( v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X3),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_27]),c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_47,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v6_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_43]),c_0_45])])).

cnf(c_0_50,negated_conjecture,
    ( v6_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_47]),c_0_50]),c_0_43]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:21:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t33_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_subset_1)).
% 0.19/0.38  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.38  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.38  fof(dt_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 0.19/0.38  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 0.19/0.38  fof(t101_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_tops_1(X2,X1)<=>v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_tops_1)).
% 0.19/0.38  fof(t108_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v5_tops_1(X2,X1)&v5_tops_1(X3,X1))=>v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tops_1)).
% 0.19/0.38  fof(t109_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v6_tops_1(X2,X1)&v6_tops_1(X3,X1))=>v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tops_1)).
% 0.19/0.38  fof(c_0_8, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|(~m1_subset_1(X16,k1_zfmisc_1(X14))|k3_subset_1(X14,k7_subset_1(X14,X15,X16))=k4_subset_1(X14,k3_subset_1(X14,X15),X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).
% 0.19/0.38  fof(c_0_9, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|k3_subset_1(X9,k3_subset_1(X9,X10))=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.38  fof(c_0_10, plain, ![X4, X5]:(~m1_subset_1(X5,k1_zfmisc_1(X4))|m1_subset_1(k3_subset_1(X4,X5),k1_zfmisc_1(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.38  cnf(c_0_11, plain, (k3_subset_1(X2,k7_subset_1(X2,X1,X3))=k4_subset_1(X2,k3_subset_1(X2,X1),X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_12, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_13, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_14, plain, (k3_subset_1(X1,k7_subset_1(X1,k3_subset_1(X1,X2),X3))=k4_subset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.19/0.38  fof(c_0_15, plain, ![X6, X7, X8]:(~m1_subset_1(X7,k1_zfmisc_1(X6))|m1_subset_1(k7_subset_1(X6,X7,X8),k1_zfmisc_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).
% 0.19/0.38  cnf(c_0_16, plain, (k3_subset_1(X1,k4_subset_1(X1,X2,X3))=k7_subset_1(X1,k3_subset_1(X1,X2),X3)|~m1_subset_1(k7_subset_1(X1,k3_subset_1(X1,X2),X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_12, c_0_14])).
% 0.19/0.38  cnf(c_0_17, plain, (m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_18, plain, (k3_subset_1(X1,k4_subset_1(X1,X2,X3))=k7_subset_1(X1,k3_subset_1(X1,X2),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_13])).
% 0.19/0.38  fof(c_0_19, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|(~m1_subset_1(X13,k1_zfmisc_1(X11))|k7_subset_1(X11,X12,X13)=k9_subset_1(X11,X12,k3_subset_1(X11,X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 0.19/0.38  cnf(c_0_20, plain, (m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(k7_subset_1(X1,k3_subset_1(X1,X2),X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.38  fof(c_0_21, plain, ![X17, X18]:((~v6_tops_1(X18,X17)|v5_tops_1(k3_subset_1(u1_struct_0(X17),X18),X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))&(~v5_tops_1(k3_subset_1(u1_struct_0(X17),X18),X17)|v6_tops_1(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_tops_1])])])])).
% 0.19/0.38  cnf(c_0_22, plain, (k7_subset_1(X1,k3_subset_1(X1,k3_subset_1(X1,X2)),X3)=k3_subset_1(X1,k3_subset_1(X1,k7_subset_1(X1,X2,X3)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_11]), c_0_13])).
% 0.19/0.38  cnf(c_0_23, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_24, plain, (m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_13])).
% 0.19/0.38  cnf(c_0_25, plain, (v6_tops_1(X2,X1)|~v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_26, plain, (k3_subset_1(X1,k3_subset_1(X1,k7_subset_1(X1,X2,X3)))=k7_subset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_22, c_0_12])).
% 0.19/0.38  cnf(c_0_27, plain, (k7_subset_1(X1,X2,k3_subset_1(X1,X3))=k9_subset_1(X1,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_12]), c_0_13])).
% 0.19/0.38  cnf(c_0_28, plain, (m1_subset_1(k3_subset_1(X1,k7_subset_1(X1,X2,X3)),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_11]), c_0_13])).
% 0.19/0.38  cnf(c_0_29, plain, (v6_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~v5_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_12]), c_0_13])).
% 0.19/0.38  cnf(c_0_30, plain, (k3_subset_1(X1,k3_subset_1(X1,k9_subset_1(X1,X2,X3)))=k9_subset_1(X1,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_13])).
% 0.19/0.38  cnf(c_0_31, plain, (m1_subset_1(k3_subset_1(X1,k9_subset_1(X1,X2,X3)),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_27]), c_0_13])).
% 0.19/0.38  fof(c_0_32, plain, ![X19, X20, X21]:(~v2_pre_topc(X19)|~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(~v5_tops_1(X20,X19)|~v5_tops_1(X21,X19)|v5_tops_1(k4_subset_1(u1_struct_0(X19),X20,X21),X19))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_tops_1])])])).
% 0.19/0.38  cnf(c_0_33, plain, (v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)|~v5_tops_1(k3_subset_1(u1_struct_0(X1),k9_subset_1(u1_struct_0(X1),X2,X3)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.38  cnf(c_0_34, plain, (v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v5_tops_1(X2,X1)|~v5_tops_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  fof(c_0_35, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v6_tops_1(X2,X1)&v6_tops_1(X3,X1))=>v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t109_tops_1])).
% 0.19/0.38  cnf(c_0_36, plain, (v6_tops_1(k7_subset_1(u1_struct_0(X1),X2,X3),X1)|~v5_tops_1(k3_subset_1(u1_struct_0(X1),k7_subset_1(u1_struct_0(X1),X2,X3)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_13])).
% 0.19/0.38  cnf(c_0_37, plain, (v5_tops_1(k3_subset_1(u1_struct_0(X1),k7_subset_1(u1_struct_0(X1),X2,X3)),X1)|~v2_pre_topc(X1)|~v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~v5_tops_1(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_11]), c_0_13])).
% 0.19/0.38  fof(c_0_38, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((v6_tops_1(esk2_0,esk1_0)&v6_tops_1(esk3_0,esk1_0))&~v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).
% 0.19/0.38  cnf(c_0_39, plain, (v6_tops_1(k7_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_pre_topc(X1)|~v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~v5_tops_1(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (~v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_41, plain, (v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_pre_topc(X1)|~v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~v5_tops_1(k3_subset_1(u1_struct_0(X1),X3),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_27]), c_0_13])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (~v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)|~v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])])).
% 0.19/0.38  cnf(c_0_47, plain, (v5_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v6_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (~v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_43]), c_0_45])])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (v6_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_47]), c_0_50]), c_0_43]), c_0_44])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 52
% 0.19/0.38  # Proof object clause steps            : 35
% 0.19/0.38  # Proof object formula steps           : 17
% 0.19/0.38  # Proof object conjectures             : 13
% 0.19/0.38  # Proof object clause conjectures      : 10
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 15
% 0.19/0.38  # Proof object initial formulas used   : 8
% 0.19/0.38  # Proof object generating inferences   : 20
% 0.19/0.38  # Proof object simplifying inferences  : 26
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 8
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 15
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 15
% 0.19/0.38  # Processed clauses                    : 140
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 53
% 0.19/0.38  # ...remaining for further processing  : 87
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 2
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 557
% 0.19/0.38  # ...of the previous two non-trivial   : 545
% 0.19/0.38  # Contextual simplify-reflections      : 49
% 0.19/0.38  # Paramodulations                      : 557
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 70
% 0.19/0.38  #    Positive orientable unit clauses  : 6
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 62
% 0.19/0.38  # Current number of unprocessed clauses: 433
% 0.19/0.38  # ...number of literals in the above   : 2522
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 17
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1780
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 704
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 104
% 0.19/0.38  # Unit Clause-clause subsumption calls : 1
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 0
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 15624
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.043 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.047 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
