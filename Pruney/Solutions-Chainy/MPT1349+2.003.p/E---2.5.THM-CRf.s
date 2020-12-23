%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:06 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  102 (23112 expanded)
%              Number of clauses        :   77 (7297 expanded)
%              Number of leaves         :   12 (5750 expanded)
%              Depth                    :   18
%              Number of atoms          :  630 (280713 expanded)
%              Number of equality atoms :   97 (65210 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   67 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_tops_2,conjecture,(
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
             => ( v3_tops_2(X3,X1,X2)
              <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4)) = k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_2)).

fof(t62_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => ( k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X2)
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(t63_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t67_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                      & v2_funct_1(X3) )
                   => k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(t73_tops_2,axiom,(
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

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t70_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_tops_2(X3,X1,X2)
               => v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
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
               => ( v3_tops_2(X3,X1,X2)
                <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                    & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4)) = k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t74_tops_2])).

fof(c_0_13,plain,(
    ! [X21,X22,X23] :
      ( ( k1_relset_1(u1_struct_0(X22),u1_struct_0(X21),k2_tops_2(u1_struct_0(X21),u1_struct_0(X22),X23)) = k2_struct_0(X22)
        | k2_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23) != k2_struct_0(X22)
        | ~ v2_funct_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | ~ l1_struct_0(X21) )
      & ( k2_relset_1(u1_struct_0(X22),u1_struct_0(X21),k2_tops_2(u1_struct_0(X21),u1_struct_0(X22),X23)) = k2_struct_0(X21)
        | k2_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23) != k2_struct_0(X22)
        | ~ v2_funct_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | ~ l1_struct_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X43] :
      ( v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
      & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
        | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
        | ~ v2_funct_1(esk5_0)
        | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) )
      & ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0)) != k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))
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
      & ( ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,X43)) = k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X43))
        | v3_tops_2(esk5_0,esk3_0,esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

fof(c_0_15,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_struct_0(X24)
      | ~ l1_struct_0(X25)
      | ~ v1_funct_1(X26)
      | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25))))
      | k2_relset_1(u1_struct_0(X24),u1_struct_0(X25),X26) != k2_struct_0(X25)
      | ~ v2_funct_1(X26)
      | v2_funct_1(k2_tops_2(u1_struct_0(X24),u1_struct_0(X25),X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_tops_2])])])).

cnf(c_0_16,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)) = k2_struct_0(X1)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v2_funct_1(esk5_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_24,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)) = k2_struct_0(X2)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_26,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ l1_struct_0(X27)
      | ~ l1_struct_0(X28)
      | ~ v1_funct_1(X29)
      | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X27)))
      | k2_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29) != k2_struct_0(X28)
      | ~ v2_funct_1(X29)
      | k7_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29,X30) = k8_relset_1(u1_struct_0(X28),u1_struct_0(X27),k2_tops_2(u1_struct_0(X27),u1_struct_0(X28),X29),X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).

cnf(c_0_27,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_30,plain,(
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

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_34,plain,
    ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X34,X35,X36,X37] :
      ( ( k1_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36) = k2_struct_0(X34)
        | ~ v3_tops_2(X36,X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( k2_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36) = k2_struct_0(X35)
        | ~ v3_tops_2(X36,X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( v2_funct_1(X36)
        | ~ v3_tops_2(X36,X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | k8_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36,k2_pre_topc(X35,X37)) = k2_pre_topc(X34,k8_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36,X37))
        | ~ v3_tops_2(X36,X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk2_3(X34,X35,X36),k1_zfmisc_1(u1_struct_0(X35)))
        | k1_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36) != k2_struct_0(X34)
        | k2_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36) != k2_struct_0(X35)
        | ~ v2_funct_1(X36)
        | v3_tops_2(X36,X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( k8_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36,k2_pre_topc(X35,esk2_3(X34,X35,X36))) != k2_pre_topc(X34,k8_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36,esk2_3(X34,X35,X36)))
        | k1_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36) != k2_struct_0(X34)
        | k2_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36) != k2_struct_0(X35)
        | ~ v2_funct_1(X36)
        | v3_tops_2(X36,X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t73_tops_2])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_37,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( v1_funct_1(k2_tops_2(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_32])])).

cnf(c_0_41,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_29])])).

cnf(c_0_42,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_22])).

fof(c_0_43,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | m1_subset_1(k2_pre_topc(X7,X8),k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v3_tops_2(X3,X1,X2)
    | v2_struct_0(X1)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_32])])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_18]),c_0_19])]),c_0_20])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_51,negated_conjecture,
    ( v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_29])])).

cnf(c_0_52,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)) = k2_struct_0(esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_32])])).

fof(c_0_53,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ v5_pre_topc(X18,X16,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | r1_tarski(k7_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,k2_pre_topc(X16,X19)),k2_pre_topc(X17,k7_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,X19)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))
        | v5_pre_topc(X18,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ r1_tarski(k7_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,k2_pre_topc(X16,esk1_3(X16,X17,X18))),k2_pre_topc(X17,k7_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,esk1_3(X16,X17,X18))))
        | v5_pre_topc(X18,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tops_2])])])])])])).

cnf(c_0_54,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_32])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_29]),c_0_32])]),c_0_21]),c_0_51]),c_0_52])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_58,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_59,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_28]),c_0_29])])).

cnf(c_0_60,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | m1_subset_1(k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_29])])).

cnf(c_0_61,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,X1)) = k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1))
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_62,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_18]),c_0_47]),c_0_46]),c_0_19]),c_0_20]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,plain,
    ( v3_tops_2(X3,X1,X2)
    | v2_struct_0(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk2_3(X1,X2,X3))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)))
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_65,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))
    | v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_66,plain,(
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

cnf(c_0_67,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X2)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,esk1_3(X1,X2,X3))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))) = k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0)
    | k2_pre_topc(esk4_0,k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))) != k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_29]),c_0_32])]),c_0_21]),c_0_51]),c_0_52]),c_0_45])).

cnf(c_0_71,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))
    | v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_56])).

cnf(c_0_72,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))) = k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))
    | v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_56])).

cnf(c_0_73,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_47]),c_0_46]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29]),c_0_69])]),c_0_21])).

cnf(c_0_75,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_76,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)
    | v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( v3_tops_2(esk5_0,esk3_0,esk4_0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])]),c_0_22]),c_0_17]),c_0_75])).

cnf(c_0_79,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_80,negated_conjecture,
    ( v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_48]),c_0_49]),c_0_50]),c_0_29]),c_0_32])]),c_0_78])).

cnf(c_0_81,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_82,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])])).

cnf(c_0_83,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_80]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])])).

cnf(c_0_84,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_85,plain,(
    ! [X31,X32,X33] :
      ( ~ l1_pre_topc(X31)
      | v2_struct_0(X32)
      | ~ l1_pre_topc(X32)
      | ~ v1_funct_1(X33)
      | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X32))
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
      | ~ v3_tops_2(X33,X31,X32)
      | v3_tops_2(k2_tops_2(u1_struct_0(X31),u1_struct_0(X32),X33),X32,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_tops_2])])])])).

cnf(c_0_86,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_82]),c_0_83]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
    | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
    | ~ v2_funct_1(esk5_0)
    | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_88,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_80]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])])).

cnf(c_0_89,plain,
    ( v2_struct_0(X2)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v3_tops_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_28]),c_0_32])])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_80])]),c_0_88]),c_0_82]),c_0_83])])).

cnf(c_0_92,plain,
    ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k2_pre_topc(X2,X1)) = k2_pre_topc(X3,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,X1))
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_tops_2(X4,X3,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_93,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_80]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_94,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_28]),c_0_29])])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_91]),c_0_29])])).

cnf(c_0_96,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0)) != k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))
    | k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk3_0)
    | k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) != k2_struct_0(esk4_0)
    | ~ v2_funct_1(esk5_0)
    | ~ v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_97,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,X1)) = k2_pre_topc(esk4_0,k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_47]),c_0_46]),c_0_48]),c_0_49]),c_0_50]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_98,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk6_0) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk6_0)) = k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0)) != k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_80])]),c_0_88]),c_0_82]),c_0_83])])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_91]),c_0_98]),c_0_99]),c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:46:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.41  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.18/0.41  # and selection function SelectCQIPrecWNTNp.
% 0.18/0.41  #
% 0.18/0.41  # Preprocessing time       : 0.031 s
% 0.18/0.41  # Presaturation interreduction done
% 0.18/0.41  
% 0.18/0.41  # Proof found!
% 0.18/0.41  # SZS status Theorem
% 0.18/0.41  # SZS output start CNFRefutation
% 0.18/0.41  fof(t74_tops_2, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4))=k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_2)).
% 0.18/0.41  fof(t62_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 0.18/0.41  fof(t63_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 0.18/0.41  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.41  fof(t67_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tops_2)).
% 0.18/0.41  fof(dt_k2_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v1_funct_1(k2_tops_2(X1,X2,X3))&v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1))&m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 0.18/0.41  fof(t73_tops_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4))=k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_2)).
% 0.18/0.41  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.18/0.41  fof(t57_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_2)).
% 0.18/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.41  fof(d5_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>((((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))&v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 0.18/0.41  fof(t70_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)=>v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_tops_2)).
% 0.18/0.41  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4))=k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))))))))), inference(assume_negation,[status(cth)],[t74_tops_2])).
% 0.18/0.41  fof(c_0_13, plain, ![X21, X22, X23]:((k1_relset_1(u1_struct_0(X22),u1_struct_0(X21),k2_tops_2(u1_struct_0(X21),u1_struct_0(X22),X23))=k2_struct_0(X22)|(k2_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23)!=k2_struct_0(X22)|~v2_funct_1(X23))|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22)))))|(v2_struct_0(X22)|~l1_struct_0(X22))|~l1_struct_0(X21))&(k2_relset_1(u1_struct_0(X22),u1_struct_0(X21),k2_tops_2(u1_struct_0(X21),u1_struct_0(X22),X23))=k2_struct_0(X21)|(k2_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23)!=k2_struct_0(X22)|~v2_funct_1(X23))|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22)))))|(v2_struct_0(X22)|~l1_struct_0(X22))|~l1_struct_0(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).
% 0.18/0.41  fof(c_0_14, negated_conjecture, ![X43]:((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&(((m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|(k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0))|~v3_tops_2(esk5_0,esk3_0,esk4_0))&(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0))!=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))|(k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0))|~v3_tops_2(esk5_0,esk3_0,esk4_0)))&((((k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0))&(k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)))&(v2_funct_1(esk5_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)))&(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(esk3_0)))|k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,X43))=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X43))|v3_tops_2(esk5_0,esk3_0,esk4_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).
% 0.18/0.41  fof(c_0_15, plain, ![X24, X25, X26]:(~l1_struct_0(X24)|(~l1_struct_0(X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25))))|(k2_relset_1(u1_struct_0(X24),u1_struct_0(X25),X26)!=k2_struct_0(X25)|~v2_funct_1(X26)|v2_funct_1(k2_tops_2(u1_struct_0(X24),u1_struct_0(X25),X26)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_tops_2])])])).
% 0.18/0.41  cnf(c_0_16, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X1)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.41  cnf(c_0_17, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_18, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_22, negated_conjecture, (v2_funct_1(esk5_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  fof(c_0_23, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.41  cnf(c_0_24, plain, (v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.41  cnf(c_0_25, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X2)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.41  fof(c_0_26, plain, ![X27, X28, X29, X30]:(~l1_struct_0(X27)|(~l1_struct_0(X28)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X27)))|(k2_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29)!=k2_struct_0(X28)|~v2_funct_1(X29)|k7_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29,X30)=k8_relset_1(u1_struct_0(X28),u1_struct_0(X27),k2_tops_2(u1_struct_0(X27),u1_struct_0(X28),X29),X30)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).
% 0.18/0.41  cnf(c_0_27, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.18/0.41  cnf(c_0_28, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.41  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  fof(c_0_30, plain, ![X13, X14, X15]:(((v1_funct_1(k2_tops_2(X13,X14,X15))|(~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))&(v1_funct_2(k2_tops_2(X13,X14,X15),X14,X13)|(~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))))&(m1_subset_1(k2_tops_2(X13,X14,X15),k1_zfmisc_1(k2_zfmisc_1(X14,X13)))|(~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).
% 0.18/0.41  cnf(c_0_31, negated_conjecture, (v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_22])).
% 0.18/0.41  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_33, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.18/0.41  cnf(c_0_34, plain, (k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.41  fof(c_0_35, plain, ![X34, X35, X36, X37]:(((((k1_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36)=k2_struct_0(X34)|~v3_tops_2(X36,X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35)))))|(~v2_pre_topc(X35)|~l1_pre_topc(X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(k2_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36)=k2_struct_0(X35)|~v3_tops_2(X36,X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35)))))|(~v2_pre_topc(X35)|~l1_pre_topc(X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34))))&(v2_funct_1(X36)|~v3_tops_2(X36,X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35)))))|(~v2_pre_topc(X35)|~l1_pre_topc(X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34))))&(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|k8_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36,k2_pre_topc(X35,X37))=k2_pre_topc(X34,k8_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36,X37))|~v3_tops_2(X36,X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35)))))|(~v2_pre_topc(X35)|~l1_pre_topc(X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34))))&((m1_subset_1(esk2_3(X34,X35,X36),k1_zfmisc_1(u1_struct_0(X35)))|(k1_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36)!=k2_struct_0(X34)|k2_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36)!=k2_struct_0(X35)|~v2_funct_1(X36))|v3_tops_2(X36,X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35)))))|(~v2_pre_topc(X35)|~l1_pre_topc(X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(k8_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36,k2_pre_topc(X35,esk2_3(X34,X35,X36)))!=k2_pre_topc(X34,k8_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36,esk2_3(X34,X35,X36)))|(k1_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36)!=k2_struct_0(X34)|k2_relset_1(u1_struct_0(X34),u1_struct_0(X35),X36)!=k2_struct_0(X35)|~v2_funct_1(X36))|v3_tops_2(X36,X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35)))))|(~v2_pre_topc(X35)|~l1_pre_topc(X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t73_tops_2])])])])])])).
% 0.18/0.41  cnf(c_0_36, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.18/0.41  cnf(c_0_37, plain, (v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.41  cnf(c_0_38, plain, (v1_funct_1(k2_tops_2(X1,X2,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.41  cnf(c_0_39, plain, (m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.41  cnf(c_0_40, negated_conjecture, (v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_32])])).
% 0.18/0.41  cnf(c_0_41, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_28]), c_0_29])])).
% 0.18/0.41  cnf(c_0_42, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_22])).
% 0.18/0.41  fof(c_0_43, plain, ![X7, X8]:(~l1_pre_topc(X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|m1_subset_1(k2_pre_topc(X7,X8),k1_zfmisc_1(u1_struct_0(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.18/0.41  cnf(c_0_44, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v3_tops_2(X3,X1,X2)|v2_struct_0(X1)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.41  cnf(c_0_45, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_32])])).
% 0.18/0.41  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_47, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_48, negated_conjecture, (v1_funct_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_19]), c_0_20])])).
% 0.18/0.41  cnf(c_0_49, negated_conjecture, (v1_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_18]), c_0_19])]), c_0_20])])).
% 0.18/0.41  cnf(c_0_50, negated_conjecture, (m1_subset_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_18]), c_0_19]), c_0_20])])).
% 0.18/0.41  cnf(c_0_51, negated_conjecture, (v2_funct_1(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_28]), c_0_29])])).
% 0.18/0.41  cnf(c_0_52, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_32])])).
% 0.18/0.41  fof(c_0_53, plain, ![X16, X17, X18, X19]:((~v5_pre_topc(X18,X16,X17)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|r1_tarski(k7_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,k2_pre_topc(X16,X19)),k2_pre_topc(X17,k7_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,X19))))|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))&((m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))|v5_pre_topc(X18,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(~r1_tarski(k7_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,k2_pre_topc(X16,esk1_3(X16,X17,X18))),k2_pre_topc(X17,k7_relset_1(u1_struct_0(X16),u1_struct_0(X17),X18,esk1_3(X16,X17,X18))))|v5_pre_topc(X18,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|(~v2_pre_topc(X16)|~l1_pre_topc(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tops_2])])])])])])).
% 0.18/0.41  cnf(c_0_54, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_28]), c_0_32])])).
% 0.18/0.41  cnf(c_0_55, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.41  cnf(c_0_56, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|m1_subset_1(esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_29]), c_0_32])]), c_0_21]), c_0_51]), c_0_52])).
% 0.18/0.41  cnf(c_0_57, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.41  fof(c_0_58, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.41  cnf(c_0_59, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|v3_tops_2(esk5_0,esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_28]), c_0_29])])).
% 0.18/0.41  cnf(c_0_60, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|m1_subset_1(k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_29])])).
% 0.18/0.41  cnf(c_0_61, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,X1))=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1))|v3_tops_2(esk5_0,esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_62, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_18]), c_0_47]), c_0_46]), c_0_19]), c_0_20]), c_0_32]), c_0_29])]), c_0_21])).
% 0.18/0.41  cnf(c_0_63, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.41  cnf(c_0_64, plain, (v3_tops_2(X3,X1,X2)|v2_struct_0(X1)|k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk2_3(X1,X2,X3)))!=k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)))|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.41  cnf(c_0_65, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))|v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.18/0.41  fof(c_0_66, plain, ![X10, X11, X12]:((((((k1_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12)=k2_struct_0(X10)|~v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10))&(k2_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12)=k2_struct_0(X11)|~v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10)))&(v2_funct_1(X12)|~v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10)))&(v5_pre_topc(X12,X10,X11)|~v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10)))&(v5_pre_topc(k2_tops_2(u1_struct_0(X10),u1_struct_0(X11),X12),X11,X10)|~v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10)))&(k1_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12)!=k2_struct_0(X10)|k2_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12)!=k2_struct_0(X11)|~v2_funct_1(X12)|~v5_pre_topc(X12,X10,X11)|~v5_pre_topc(k2_tops_2(u1_struct_0(X10),u1_struct_0(X11),X12),X11,X10)|v3_tops_2(X12,X10,X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))))|~l1_pre_topc(X11)|~l1_pre_topc(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).
% 0.18/0.41  cnf(c_0_67, plain, (v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|~r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,esk1_3(X1,X2,X3))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.41  cnf(c_0_68, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)))=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)))|v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.18/0.41  cnf(c_0_69, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_63])).
% 0.18/0.41  cnf(c_0_70, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)|k2_pre_topc(esk4_0,k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_29]), c_0_32])]), c_0_21]), c_0_51]), c_0_52]), c_0_45])).
% 0.18/0.41  cnf(c_0_71, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)))|v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_56])).
% 0.18/0.41  cnf(c_0_72, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk4_0,esk3_0,k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0))))|v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_56])).
% 0.18/0.41  cnf(c_0_73, plain, (v3_tops_2(X3,X1,X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v5_pre_topc(X3,X1,X2)|~v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.18/0.41  cnf(c_0_74, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_47]), c_0_46]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29]), c_0_69])]), c_0_21])).
% 0.18/0.41  cnf(c_0_75, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_76, plain, (v5_pre_topc(X1,X2,X3)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.18/0.41  cnf(c_0_77, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)|v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.18/0.41  cnf(c_0_78, negated_conjecture, (v3_tops_2(esk5_0,esk3_0,esk4_0)|~v5_pre_topc(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])]), c_0_22]), c_0_17]), c_0_75])).
% 0.18/0.41  cnf(c_0_79, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.18/0.41  cnf(c_0_80, negated_conjecture, (v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_48]), c_0_49]), c_0_50]), c_0_29]), c_0_32])]), c_0_78])).
% 0.18/0.41  cnf(c_0_81, plain, (v2_funct_1(X1)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.18/0.41  cnf(c_0_82, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])])).
% 0.18/0.41  cnf(c_0_83, negated_conjecture, (v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_80]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])])).
% 0.18/0.41  cnf(c_0_84, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.18/0.41  fof(c_0_85, plain, ![X31, X32, X33]:(~l1_pre_topc(X31)|(v2_struct_0(X32)|~l1_pre_topc(X32)|(~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X32))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))|(~v3_tops_2(X33,X31,X32)|v3_tops_2(k2_tops_2(u1_struct_0(X31),u1_struct_0(X32),X33),X32,X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_tops_2])])])])).
% 0.18/0.41  cnf(c_0_86, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|~l1_struct_0(esk4_0)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_82]), c_0_83]), c_0_18]), c_0_19]), c_0_20])])).
% 0.18/0.41  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0)|~v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_88, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_80]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])])).
% 0.18/0.41  cnf(c_0_89, plain, (v2_struct_0(X2)|v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v3_tops_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.18/0.41  cnf(c_0_90, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_28]), c_0_32])])).
% 0.18/0.41  cnf(c_0_91, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_80])]), c_0_88]), c_0_82]), c_0_83])])).
% 0.18/0.41  cnf(c_0_92, plain, (k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k2_pre_topc(X2,X1))=k2_pre_topc(X3,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,X1))|v2_struct_0(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_tops_2(X4,X3,X2)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.41  cnf(c_0_93, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_80]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])]), c_0_21])).
% 0.18/0.41  cnf(c_0_94, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_28]), c_0_29])])).
% 0.18/0.41  cnf(c_0_95, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_91]), c_0_29])])).
% 0.18/0.41  cnf(c_0_96, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0))!=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))|k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk3_0)|k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)!=k2_struct_0(esk4_0)|~v2_funct_1(esk5_0)|~v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_97, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,X1))=k2_pre_topc(esk4_0,k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_47]), c_0_46]), c_0_48]), c_0_49]), c_0_50]), c_0_32]), c_0_29])]), c_0_21])).
% 0.18/0.41  cnf(c_0_98, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),esk6_0)=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_94, c_0_91])).
% 0.18/0.41  cnf(c_0_99, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0),k2_pre_topc(esk3_0,esk6_0))=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.18/0.41  cnf(c_0_100, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk3_0,esk6_0))!=k2_pre_topc(esk4_0,k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_80])]), c_0_88]), c_0_82]), c_0_83])])).
% 0.18/0.41  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_91]), c_0_98]), c_0_99]), c_0_100]), ['proof']).
% 0.18/0.41  # SZS output end CNFRefutation
% 0.18/0.41  # Proof object total steps             : 102
% 0.18/0.41  # Proof object clause steps            : 77
% 0.18/0.41  # Proof object formula steps           : 25
% 0.18/0.41  # Proof object conjectures             : 58
% 0.18/0.41  # Proof object clause conjectures      : 55
% 0.18/0.41  # Proof object formula conjectures     : 3
% 0.18/0.41  # Proof object initial clauses used    : 35
% 0.18/0.41  # Proof object initial formulas used   : 12
% 0.18/0.41  # Proof object generating inferences   : 39
% 0.18/0.41  # Proof object simplifying inferences  : 169
% 0.18/0.41  # Training examples: 0 positive, 0 negative
% 0.18/0.41  # Parsed axioms                        : 12
% 0.18/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.41  # Initial clauses                      : 42
% 0.18/0.41  # Removed in clause preprocessing      : 0
% 0.18/0.41  # Initial clauses in saturation        : 42
% 0.18/0.41  # Processed clauses                    : 311
% 0.18/0.41  # ...of these trivial                  : 1
% 0.18/0.41  # ...subsumed                          : 20
% 0.18/0.41  # ...remaining for further processing  : 289
% 0.18/0.41  # Other redundant clauses eliminated   : 2
% 0.18/0.41  # Clauses deleted for lack of memory   : 0
% 0.18/0.41  # Backward-subsumed                    : 56
% 0.18/0.41  # Backward-rewritten                   : 100
% 0.18/0.41  # Generated clauses                    : 510
% 0.18/0.41  # ...of the previous two non-trivial   : 503
% 0.18/0.41  # Contextual simplify-reflections      : 26
% 0.18/0.41  # Paramodulations                      : 508
% 0.18/0.41  # Factorizations                       : 0
% 0.18/0.41  # Equation resolutions                 : 2
% 0.18/0.41  # Propositional unsat checks           : 0
% 0.18/0.41  #    Propositional check models        : 0
% 0.18/0.41  #    Propositional check unsatisfiable : 0
% 0.18/0.41  #    Propositional clauses             : 0
% 0.18/0.41  #    Propositional clauses after purity: 0
% 0.18/0.41  #    Propositional unsat core size     : 0
% 0.18/0.41  #    Propositional preprocessing time  : 0.000
% 0.18/0.41  #    Propositional encoding time       : 0.000
% 0.18/0.41  #    Propositional solver time         : 0.000
% 0.18/0.41  #    Success case prop preproc time    : 0.000
% 0.18/0.41  #    Success case prop encoding time   : 0.000
% 0.18/0.41  #    Success case prop solver time     : 0.000
% 0.18/0.41  # Current number of processed clauses  : 93
% 0.18/0.41  #    Positive orientable unit clauses  : 54
% 0.18/0.41  #    Positive unorientable unit clauses: 0
% 0.18/0.41  #    Negative unit clauses             : 3
% 0.18/0.41  #    Non-unit-clauses                  : 36
% 0.18/0.41  # Current number of unprocessed clauses: 65
% 0.18/0.41  # ...number of literals in the above   : 100
% 0.18/0.41  # Current number of archived formulas  : 0
% 0.18/0.41  # Current number of archived clauses   : 194
% 0.18/0.41  # Clause-clause subsumption calls (NU) : 5923
% 0.18/0.41  # Rec. Clause-clause subsumption calls : 1606
% 0.18/0.41  # Non-unit clause-clause subsumptions  : 102
% 0.18/0.41  # Unit Clause-clause subsumption calls : 395
% 0.18/0.41  # Rewrite failures with RHS unbound    : 0
% 0.18/0.41  # BW rewrite match attempts            : 188
% 0.18/0.41  # BW rewrite match successes           : 8
% 0.18/0.41  # Condensation attempts                : 0
% 0.18/0.41  # Condensation successes               : 0
% 0.18/0.41  # Termbank termtop insertions          : 39666
% 0.18/0.41  
% 0.18/0.41  # -------------------------------------------------
% 0.18/0.41  # User time                : 0.072 s
% 0.18/0.41  # System time              : 0.006 s
% 0.18/0.41  # Total time               : 0.078 s
% 0.18/0.41  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
