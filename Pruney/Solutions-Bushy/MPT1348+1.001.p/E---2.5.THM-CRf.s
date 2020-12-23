%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1348+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:10 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 (22267 expanded)
%              Number of clauses        :   72 (6901 expanded)
%              Number of leaves         :    9 (5480 expanded)
%              Depth                    :   17
%              Number of atoms          :  481 (284876 expanded)
%              Number of equality atoms :   59 (64393 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   46 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_tops_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_tops_2(X3,X1,X2)
              <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_2)).

fof(t56_tops_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).

fof(t68_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                      & v2_funct_1(X3) )
                   => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tops_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(d5_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_tops_2(X3,X1,X2)
              <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & v5_pre_topc(X3,X1,X2)
                  & v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

fof(t57_tops_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_2)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( v3_tops_2(X3,X1,X2)
                <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                    & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                       => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t73_tops_2])).

fof(c_0_10,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ v5_pre_topc(X18,X16,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | r1_tarski(k2_pre_topc(X16,k8_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,X19)),k8_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,k2_pre_topc(X17,X19)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X17)))
        | v5_pre_topc(X18,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ r1_tarski(k2_pre_topc(X16,k8_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,esk1_3(X16,X17,X18))),k8_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,k2_pre_topc(X17,esk1_3(X16,X17,X18))))
        | v5_pre_topc(X18,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X34] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
      & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
        | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
        | ~ v2_funct_1(esk5_0)
        | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) )
      & ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0)) != k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))
        | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
        | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
        | ~ v2_funct_1(esk5_0)
        | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) )
      & ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0)
        | v3_tops_2(esk5_0,esk3_0,esk4_0) )
      & ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0)
        | v3_tops_2(esk5_0,esk3_0,esk4_0) )
      & ( v2_funct_1(esk5_0)
        | v3_tops_2(esk5_0,esk3_0,esk4_0) )
      & ( ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,X34)) = k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X34))
        | v3_tops_2(esk5_0,esk3_0,esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

fof(c_0_12,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ l1_struct_0(X26)
      | ~ l1_struct_0(X27)
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
      | k2_relset_1(u1_struct_0(X26),u1_struct_0(X27),X28) != k2_struct_0(X27)
      | ~ v2_funct_1(X28)
      | k8_relset_1(u1_struct_0(X26),u1_struct_0(X27),X28,X29) = k7_relset_1(u1_struct_0(X27),u1_struct_0(X26),k2_tops_2(u1_struct_0(X26),u1_struct_0(X27),X28),X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_tops_2])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_22,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( v2_funct_1(esk5_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_25,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | l1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_26,plain,(
    ! [X12,X13,X14] :
      ( ( v1_funct_1(k2_tops_2(X12,X13,X14))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( v1_funct_2(k2_tops_2(X12,X13,X14),X13,X12)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( m1_subset_1(k2_tops_2(X12,X13,X14),k1_zfmisc_1(k2_zfmisc_1(X13,X12)))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

fof(c_0_27,plain,(
    ! [X7,X8,X9] :
      ( ( k1_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9) = k2_struct_0(X7)
        | ~ v3_tops_2(X9,X7,X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( k2_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9) = k2_struct_0(X8)
        | ~ v3_tops_2(X9,X7,X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( v2_funct_1(X9)
        | ~ v3_tops_2(X9,X7,X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( v5_pre_topc(X9,X7,X8)
        | ~ v3_tops_2(X9,X7,X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X7),u1_struct_0(X8),X9),X8,X7)
        | ~ v3_tops_2(X9,X7,X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( k1_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9) != k2_struct_0(X7)
        | k2_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9) != k2_struct_0(X8)
        | ~ v2_funct_1(X9)
        | ~ v5_pre_topc(X9,X7,X8)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X7),u1_struct_0(X8),X9),X8,X7)
        | v3_tops_2(X9,X7,X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

cnf(c_0_28,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,X1)) = k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1))
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_17]),c_0_14]),c_0_18])]),c_0_24])).

cnf(c_0_32,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X21,X22,X23,X24] :
      ( ( ~ v5_pre_topc(X23,X21,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | r1_tarski(k7_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23,k2_pre_topc(X21,X24)),k2_pre_topc(X22,k7_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23,X24)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk2_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))
        | v5_pre_topc(X23,X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r1_tarski(k7_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23,k2_pre_topc(X21,esk2_3(X21,X22,X23))),k2_pre_topc(X22,k7_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23,esk2_3(X21,X22,X23))))
        | v5_pre_topc(X23,X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tops_2])])])])])])).

cnf(c_0_34,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v1_funct_1(k2_tops_2(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( v3_tops_2(X3,X1,X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk1_3(X1,X2,X3))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))) = k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_19])])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_14]),c_0_17]),c_0_18])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_14]),c_0_17]),c_0_18])])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_14]),c_0_17]),c_0_18])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | ~ v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_17]),c_0_14]),c_0_18]),c_0_19]),c_0_20])]),c_0_24]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_15]),c_0_16]),c_0_17]),c_0_14]),c_0_18]),c_0_19]),c_0_20]),c_0_41])])).

fof(c_0_50,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | m1_subset_1(k2_pre_topc(X10,X11),k1_zfmisc_1(u1_struct_0(X10))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_51,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_32]),c_0_20])])).

cnf(c_0_52,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | m1_subset_1(esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_16]),c_0_15]),c_0_45]),c_0_46]),c_0_20]),c_0_19])]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X2)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,esk2_3(X1,X2,X3))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))) = k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | m1_subset_1(k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_19])])).

cnf(c_0_58,negated_conjecture,
    ( v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))),k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_16]),c_0_15]),c_0_45]),c_0_44]),c_0_46]),c_0_20]),c_0_19])]),c_0_47]),c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))) = k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_57]),c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ r1_tarski(k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))),k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))) = k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_52])).

cnf(c_0_62,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_41])]),c_0_53])).

cnf(c_0_64,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_17]),c_0_14]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_66,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_63]),c_0_17]),c_0_14]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_67,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_68,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_69,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_65]),c_0_66]),c_0_17]),c_0_14]),c_0_18])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
    | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
    | ~ v2_funct_1(esk5_0)
    | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_71,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_63]),c_0_17]),c_0_14]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_72,plain,
    ( r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4)),k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,k2_pre_topc(X3,X4)))
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_73,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_63]),c_0_17]),c_0_14]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_74,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_32]),c_0_19])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_63])]),c_0_71]),c_0_65]),c_0_66])])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)),k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_15]),c_0_16]),c_0_17]),c_0_14]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_78,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0)) != k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))
    | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
    | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
    | ~ v2_funct_1(esk5_0)
    | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_79,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,k2_pre_topc(X2,X4)),k2_pre_topc(X3,k7_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4)))
    | v2_struct_0(X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_80,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_63]),c_0_17]),c_0_14]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_81,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_32]),c_0_20])])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk4_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_76]),c_0_19])])).

cnf(c_0_83,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)),k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0)) != k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_63])]),c_0_71]),c_0_65]),c_0_66])])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk4_0,X1)),k2_pre_topc(esk3_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_16]),c_0_15]),c_0_45]),c_0_44]),c_0_46]),c_0_20]),c_0_19])]),c_0_47])).

cnf(c_0_87,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk4_0,esk6_0)) = k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk6_0) = k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_76])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0)),k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_76]),c_0_87]),c_0_88]),c_0_89]),
    [proof]).

%------------------------------------------------------------------------------
