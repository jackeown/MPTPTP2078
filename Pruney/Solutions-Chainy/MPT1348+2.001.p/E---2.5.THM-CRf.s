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
% DateTime   : Thu Dec  3 11:14:05 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
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
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
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
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_26,plain,(
    ! [X13,X14,X15] :
      ( ( v1_funct_1(k2_tops_2(X13,X14,X15))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v1_funct_2(k2_tops_2(X13,X14,X15),X14,X13)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( m1_subset_1(k2_tops_2(X13,X14,X15),k1_zfmisc_1(k2_zfmisc_1(X14,X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

fof(c_0_27,plain,(
    ! [X10,X11,X12] :
      ( ( k1_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12) = k2_struct_0(X10)
        | ~ v3_tops_2(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( k2_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12) = k2_struct_0(X11)
        | ~ v3_tops_2(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( v2_funct_1(X12)
        | ~ v3_tops_2(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( v5_pre_topc(X12,X10,X11)
        | ~ v3_tops_2(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X10),u1_struct_0(X11),X12),X11,X10)
        | ~ v3_tops_2(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( k1_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12) != k2_struct_0(X10)
        | k2_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12) != k2_struct_0(X11)
        | ~ v2_funct_1(X12)
        | ~ v5_pre_topc(X12,X10,X11)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X10),u1_struct_0(X11),X12),X11,X10)
        | v3_tops_2(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) ) ) ),
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
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_14]),c_0_17]),c_0_18])]),c_0_24])).

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
    ( v1_funct_1(k2_tops_2(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
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
    ( v1_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_14]),c_0_17]),c_0_18])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_14]),c_0_17]),c_0_18])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | ~ v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_14]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_24]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_15]),c_0_16]),c_0_14]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_41])])).

fof(c_0_50,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | m1_subset_1(k2_pre_topc(X7,X8),k1_zfmisc_1(u1_struct_0(X7))) ) ),
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
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_16]),c_0_15]),c_0_44]),c_0_45]),c_0_46]),c_0_20]),c_0_19])]),c_0_47]),c_0_53])).

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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_14]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_66,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_63]),c_0_14]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_65]),c_0_66]),c_0_14]),c_0_17]),c_0_18])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
    | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
    | ~ v2_funct_1(esk5_0)
    | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_71,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_63]),c_0_14]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_63]),c_0_14]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_15]),c_0_16]),c_0_14]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_63]),c_0_14]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

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
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_16]),c_0_15]),c_0_44]),c_0_45]),c_0_46]),c_0_20]),c_0_19])]),c_0_47])).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:34:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.40  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t73_tops_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4))=k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_2)).
% 0.19/0.40  fof(t56_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_2)).
% 0.19/0.40  fof(t68_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tops_2)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.40  fof(dt_k2_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v1_funct_1(k2_tops_2(X1,X2,X3))&v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1))&m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 0.19/0.40  fof(d5_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>((((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))&v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 0.19/0.40  fof(t57_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_2)).
% 0.19/0.40  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.19/0.40  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4))=k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))))))))), inference(assume_negation,[status(cth)],[t73_tops_2])).
% 0.19/0.40  fof(c_0_10, plain, ![X16, X17, X18, X19]:((~v5_pre_topc(X18,X16,X17)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|r1_tarski(k2_pre_topc(X16,k8_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,X19)),k8_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,k2_pre_topc(X17,X19))))|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))&((m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X17)))|v5_pre_topc(X18,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(~r1_tarski(k2_pre_topc(X16,k8_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,esk1_3(X16,X17,X18))),k8_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,k2_pre_topc(X17,esk1_3(X16,X17,X18))))|v5_pre_topc(X18,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))|(~v2_pre_topc(X16)|~l1_pre_topc(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).
% 0.19/0.40  fof(c_0_11, negated_conjecture, ![X34]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&(((m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))|(k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0))|~v3_tops_2(esk5_0,esk3_0,esk4_0))&(k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0))!=k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))|(k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0))|~v3_tops_2(esk5_0,esk3_0,esk4_0)))&((((k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0))&(k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)))&(v2_funct_1(esk5_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)))&(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(esk4_0)))|k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,X34))=k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X34))|v3_tops_2(esk5_0,esk3_0,esk4_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).
% 0.19/0.40  fof(c_0_12, plain, ![X26, X27, X28, X29]:(~l1_struct_0(X26)|(~l1_struct_0(X27)|(~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|(k2_relset_1(u1_struct_0(X26),u1_struct_0(X27),X28)!=k2_struct_0(X27)|~v2_funct_1(X28)|k8_relset_1(u1_struct_0(X26),u1_struct_0(X27),X28,X29)=k7_relset_1(u1_struct_0(X27),u1_struct_0(X26),k2_tops_2(u1_struct_0(X26),u1_struct_0(X27),X28),X29)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_tops_2])])])).
% 0.19/0.40  cnf(c_0_13, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_14, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_15, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  fof(c_0_21, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  cnf(c_0_22, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (v2_funct_1(esk5_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  fof(c_0_25, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.40  fof(c_0_26, plain, ![X13, X14, X15]:(((v1_funct_1(k2_tops_2(X13,X14,X15))|(~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))&(v1_funct_2(k2_tops_2(X13,X14,X15),X14,X13)|(~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))))&(m1_subset_1(k2_tops_2(X13,X14,X15),k1_zfmisc_1(k2_zfmisc_1(X14,X13)))|(~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).
% 0.19/0.40  fof(c_0_27, plain, ![X10, X11, X12]:((((((k1_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12)=k2_struct_0(X10)|~v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10))&(k2_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12)=k2_struct_0(X11)|~v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10)))&(v2_funct_1(X12)|~v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10)))&(v5_pre_topc(X12,X10,X11)|~v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10)))&(v5_pre_topc(k2_tops_2(u1_struct_0(X10),u1_struct_0(X11),X12),X11,X10)|~v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10)))&(k1_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12)!=k2_struct_0(X10)|k2_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12)!=k2_struct_0(X11)|~v2_funct_1(X12)|~v5_pre_topc(X12,X10,X11)|~v5_pre_topc(k2_tops_2(u1_struct_0(X10),u1_struct_0(X11),X12),X11,X10)|v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,X1))=k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1))|v3_tops_2(esk5_0,esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_14]), c_0_17]), c_0_18])]), c_0_24])).
% 0.19/0.40  cnf(c_0_32, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  fof(c_0_33, plain, ![X21, X22, X23, X24]:((~v5_pre_topc(X23,X21,X22)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|r1_tarski(k7_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23,k2_pre_topc(X21,X24)),k2_pre_topc(X22,k7_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23,X24))))|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22)))))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&((m1_subset_1(esk2_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))|v5_pre_topc(X23,X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22)))))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~r1_tarski(k7_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23,k2_pre_topc(X21,esk2_3(X21,X22,X23))),k2_pre_topc(X22,k7_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23,esk2_3(X21,X22,X23))))|v5_pre_topc(X23,X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22)))))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tops_2])])])])])])).
% 0.19/0.40  cnf(c_0_34, plain, (v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_35, plain, (v1_funct_1(k2_tops_2(X1,X2,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_36, plain, (m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_37, plain, (v3_tops_2(X3,X1,X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v5_pre_topc(X3,X1,X2)|~v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_39, plain, (v5_pre_topc(X3,X1,X2)|~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk1_3(X1,X2,X3))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0)))=k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)))|v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.40  cnf(c_0_41, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_19])])).
% 0.19/0.40  cnf(c_0_43, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (v1_funct_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_14]), c_0_17]), c_0_18])])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (v1_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_14]), c_0_17]), c_0_18])])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (m1_subset_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_14]), c_0_17]), c_0_18])])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (v3_tops_2(esk5_0,esk3_0,esk4_0)|~v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|~v5_pre_topc(esk5_0,esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_14]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_24]), c_0_23])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_15]), c_0_16]), c_0_14]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_41])])).
% 0.19/0.40  fof(c_0_50, plain, ![X7, X8]:(~l1_pre_topc(X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|m1_subset_1(k2_pre_topc(X7,X8),k1_zfmisc_1(u1_struct_0(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_32]), c_0_20])])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|m1_subset_1(esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_16]), c_0_15]), c_0_45]), c_0_46]), c_0_20]), c_0_19])]), c_0_47])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (v3_tops_2(esk5_0,esk3_0,esk4_0)|~v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.40  cnf(c_0_54, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.40  cnf(c_0_55, plain, (v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|~r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,esk2_3(X1,X2,X3))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|m1_subset_1(k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_52]), c_0_19])])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (v3_tops_2(esk5_0,esk3_0,esk4_0)|~r1_tarski(k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))),k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_16]), c_0_15]), c_0_44]), c_0_45]), c_0_46]), c_0_20]), c_0_19])]), c_0_47]), c_0_53])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_57]), c_0_53])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (v3_tops_2(esk5_0,esk3_0,esk4_0)|~r1_tarski(k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))),k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))=k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))|v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_52])).
% 0.19/0.40  cnf(c_0_62, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_41])]), c_0_53])).
% 0.19/0.40  cnf(c_0_64, plain, (v2_funct_1(X1)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_65, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_14]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_63]), c_0_14]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_67, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_68, plain, (v5_pre_topc(X1,X2,X3)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|~l1_struct_0(esk4_0)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_65]), c_0_66]), c_0_14]), c_0_17]), c_0_18])])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))|k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0)|~v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_63]), c_0_14]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_72, plain, (r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4)),k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,k2_pre_topc(X3,X4)))|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_63]), c_0_14]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_74, plain, (v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_32]), c_0_19])])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_63])]), c_0_71]), c_0_65]), c_0_66])])).
% 0.19/0.40  cnf(c_0_77, negated_conjecture, (r1_tarski(k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)),k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,X1)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_15]), c_0_16]), c_0_14]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0))!=k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))|k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0)|~v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_79, plain, (r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,k2_pre_topc(X2,X4)),k2_pre_topc(X3,k7_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4)))|v2_struct_0(X3)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_80, negated_conjecture, (v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_63]), c_0_14]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_81, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_32]), c_0_20])])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (m1_subset_1(k2_pre_topc(esk4_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_76]), c_0_19])])).
% 0.19/0.40  cnf(c_0_83, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (r1_tarski(k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)),k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_77, c_0_76])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0))!=k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_63])]), c_0_71]), c_0_65]), c_0_66])])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, (r1_tarski(k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk4_0,X1)),k2_pre_topc(esk3_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_16]), c_0_15]), c_0_44]), c_0_45]), c_0_46]), c_0_20]), c_0_19])]), c_0_47])).
% 0.19/0.40  cnf(c_0_87, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk4_0,esk6_0))=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.40  cnf(c_0_88, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk6_0)=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_81, c_0_76])).
% 0.19/0.40  cnf(c_0_89, negated_conjecture, (~r1_tarski(k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,esk6_0)),k2_pre_topc(esk3_0,k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.19/0.40  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_76]), c_0_87]), c_0_88]), c_0_89]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 91
% 0.19/0.40  # Proof object clause steps            : 72
% 0.19/0.40  # Proof object formula steps           : 19
% 0.19/0.40  # Proof object conjectures             : 54
% 0.19/0.40  # Proof object clause conjectures      : 51
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 34
% 0.19/0.40  # Proof object initial formulas used   : 9
% 0.19/0.40  # Proof object generating inferences   : 35
% 0.19/0.40  # Proof object simplifying inferences  : 142
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 9
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 35
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 35
% 0.19/0.40  # Processed clauses                    : 207
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 6
% 0.19/0.40  # ...remaining for further processing  : 201
% 0.19/0.40  # Other redundant clauses eliminated   : 2
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 7
% 0.19/0.40  # Backward-rewritten                   : 86
% 0.19/0.40  # Generated clauses                    : 322
% 0.19/0.40  # ...of the previous two non-trivial   : 303
% 0.19/0.40  # Contextual simplify-reflections      : 14
% 0.19/0.40  # Paramodulations                      : 320
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 2
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 72
% 0.19/0.40  #    Positive orientable unit clauses  : 40
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 3
% 0.19/0.40  #    Non-unit-clauses                  : 29
% 0.19/0.40  # Current number of unprocessed clauses: 98
% 0.19/0.40  # ...number of literals in the above   : 235
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 127
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 3593
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1544
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 27
% 0.19/0.40  # Unit Clause-clause subsumption calls : 375
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 102
% 0.19/0.40  # BW rewrite match successes           : 5
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 23764
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.056 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.060 s
% 0.19/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
