%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:06 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  110 (49656 expanded)
%              Number of clauses        :   85 (15739 expanded)
%              Number of leaves         :   12 (12323 expanded)
%              Depth                    :   24
%              Number of atoms          :  691 (601593 expanded)
%              Number of equality atoms :   94 (139277 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_2)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).

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
    ! [X24,X25,X26] :
      ( ( k1_relset_1(u1_struct_0(X25),u1_struct_0(X24),k2_tops_2(u1_struct_0(X24),u1_struct_0(X25),X26)) = k2_struct_0(X25)
        | k2_relset_1(u1_struct_0(X24),u1_struct_0(X25),X26) != k2_struct_0(X25)
        | ~ v2_funct_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25))))
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | ~ l1_struct_0(X24) )
      & ( k2_relset_1(u1_struct_0(X25),u1_struct_0(X24),k2_tops_2(u1_struct_0(X24),u1_struct_0(X25),X26)) = k2_struct_0(X24)
        | k2_relset_1(u1_struct_0(X24),u1_struct_0(X25),X26) != k2_struct_0(X25)
        | ~ v2_funct_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25))))
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | ~ l1_struct_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X46] :
      ( v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & ~ v2_struct_0(esk5_0)
      & v2_pre_topc(esk5_0)
      & l1_pre_topc(esk5_0)
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk4_0)
        | k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk5_0)
        | ~ v2_funct_1(esk6_0)
        | ~ v3_tops_2(esk6_0,esk4_0,esk5_0) )
      & ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0)) != k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0))
        | k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk4_0)
        | k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk5_0)
        | ~ v2_funct_1(esk6_0)
        | ~ v3_tops_2(esk6_0,esk4_0,esk5_0) )
      & ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_struct_0(esk4_0)
        | v3_tops_2(esk6_0,esk4_0,esk5_0) )
      & ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_struct_0(esk5_0)
        | v3_tops_2(esk6_0,esk4_0,esk5_0) )
      & ( v2_funct_1(esk6_0)
        | v3_tops_2(esk6_0,esk4_0,esk5_0) )
      & ( ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,X46)) = k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X46))
        | v3_tops_2(esk6_0,esk4_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

fof(c_0_15,plain,(
    ! [X27,X28,X29] :
      ( ~ l1_struct_0(X27)
      | ~ l1_struct_0(X28)
      | ~ v1_funct_1(X29)
      | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
      | k2_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29) != k2_struct_0(X28)
      | ~ v2_funct_1(X29)
      | v2_funct_1(k2_tops_2(u1_struct_0(X27),u1_struct_0(X28),X29)) ) ),
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
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_struct_0(esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v2_funct_1(esk6_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
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
    ! [X30,X31,X32,X33] :
      ( ~ l1_struct_0(X30)
      | ~ l1_struct_0(X31)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))
      | k2_relset_1(u1_struct_0(X30),u1_struct_0(X31),X32) != k2_struct_0(X31)
      | ~ v2_funct_1(X32)
      | k7_relset_1(u1_struct_0(X30),u1_struct_0(X31),X32,X33) = k8_relset_1(u1_struct_0(X31),u1_struct_0(X30),k2_tops_2(u1_struct_0(X30),u1_struct_0(X31),X32),X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).

cnf(c_0_27,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)) = k2_struct_0(esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_30,plain,(
    ! [X11,X12,X13] :
      ( ( v1_funct_1(k2_tops_2(X11,X12,X13))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( v1_funct_2(k2_tops_2(X11,X12,X13),X12,X11)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( m1_subset_1(k2_tops_2(X11,X12,X13),k1_zfmisc_1(k2_zfmisc_1(X12,X11)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)) = k2_struct_0(esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk5_0) ),
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
    ! [X37,X38,X39,X40] :
      ( ( k1_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39) = k2_struct_0(X37)
        | ~ v3_tops_2(X39,X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( k2_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39) = k2_struct_0(X38)
        | ~ v3_tops_2(X39,X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( v2_funct_1(X39)
        | ~ v3_tops_2(X39,X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,k2_pre_topc(X38,X40)) = k2_pre_topc(X37,k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,X40))
        | ~ v3_tops_2(X39,X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( m1_subset_1(esk3_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X38)))
        | k1_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39) != k2_struct_0(X37)
        | k2_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39) != k2_struct_0(X38)
        | ~ v2_funct_1(X39)
        | v3_tops_2(X39,X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,k2_pre_topc(X38,esk3_3(X37,X38,X39))) != k2_pre_topc(X37,k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,esk3_3(X37,X38,X39)))
        | k1_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39) != k2_struct_0(X37)
        | k2_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39) != k2_struct_0(X38)
        | ~ v2_funct_1(X39)
        | v3_tops_2(X39,X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t73_tops_2])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)) = k2_struct_0(esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk5_0) ),
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
    ( v2_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_32])])).

cnf(c_0_41,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)) = k2_struct_0(esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_29])])).

cnf(c_0_42,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_22])).

fof(c_0_43,plain,(
    ! [X5,X6] :
      ( ~ l1_pre_topc(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | m1_subset_1(k2_pre_topc(X5,X6),k1_zfmisc_1(u1_struct_0(X5))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
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
    ( k1_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)) = k2_struct_0(esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_32])])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_18]),c_0_19])]),c_0_20])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_51,negated_conjecture,
    ( v2_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_29])])).

cnf(c_0_52,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)) = k2_struct_0(esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_32])])).

cnf(c_0_53,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_32])])).

cnf(c_0_54,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | m1_subset_1(esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_29]),c_0_32])]),c_0_21]),c_0_51]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_28]),c_0_29])])).

cnf(c_0_57,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | m1_subset_1(k2_pre_topc(esk4_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_29])])).

cnf(c_0_58,plain,
    ( v3_tops_2(X3,X1,X2)
    | v2_struct_0(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk3_3(X1,X2,X3))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3)))
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

cnf(c_0_59,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))
    | v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,X1)) = k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1))
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_61,plain,(
    ! [X8,X9,X10] :
      ( ( k1_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10) = k2_struct_0(X8)
        | ~ v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( k2_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10) = k2_struct_0(X9)
        | ~ v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( v2_funct_1(X10)
        | ~ v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( v5_pre_topc(X10,X8,X9)
        | ~ v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X8),u1_struct_0(X9),X10),X9,X8)
        | ~ v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( k1_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10) != k2_struct_0(X8)
        | k2_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10) != k2_struct_0(X9)
        | ~ v2_funct_1(X10)
        | ~ v5_pre_topc(X10,X8,X9)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X8),u1_struct_0(X9),X10),X9,X8)
        | v3_tops_2(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

cnf(c_0_62,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))) != k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_29]),c_0_32])]),c_0_21]),c_0_51]),c_0_52]),c_0_45])).

cnf(c_0_63,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))
    | v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))) = k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))
    | v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_55])).

fof(c_0_65,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ v5_pre_topc(X21,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | r1_tarski(k7_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,k2_pre_topc(X19,X22)),k2_pre_topc(X20,k7_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,X22)))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk2_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))
        | v5_pre_topc(X21,X19,X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r1_tarski(k7_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,k2_pre_topc(X19,esk2_3(X19,X20,X21))),k2_pre_topc(X20,k7_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,esk2_3(X19,X20,X21))))
        | v5_pre_topc(X21,X19,X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tops_2])])])])])])).

fof(c_0_66,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ v5_pre_topc(X16,X14,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | r1_tarski(k2_pre_topc(X14,k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,X17)),k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,k2_pre_topc(X15,X17)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk1_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X15)))
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r1_tarski(k2_pre_topc(X14,k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,esk1_3(X14,X15,X16))),k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,k2_pre_topc(X15,esk1_3(X14,X15,X16))))
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).

cnf(c_0_67,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_69,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_48]),c_0_49]),c_0_50]),c_0_29]),c_0_32])])).

cnf(c_0_72,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_18]),c_0_47]),c_0_46]),c_0_19]),c_0_20]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)),k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,X1)))
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_29]),c_0_32])])).

cnf(c_0_74,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | m1_subset_1(k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_72]),c_0_29])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk2_3(esk4_0,esk5_0,esk6_0))),k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0))))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0))) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0)))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk2_3(esk4_0,esk5_0,esk6_0))),k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0))))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_78,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk2_3(esk4_0,esk5_0,esk6_0)) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_72])).

cnf(c_0_79,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_80,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0))) = k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0)))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_72])).

cnf(c_0_81,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_82,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_struct_0(esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0))),k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0))))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ r1_tarski(k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0))),k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_47]),c_0_46]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_85,negated_conjecture,
    ( v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])]),c_0_22]),c_0_17])).

cnf(c_0_86,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_80]),c_0_84])).

cnf(c_0_87,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_88,negated_conjecture,
    ( v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_71])).

cnf(c_0_89,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_90,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])])).

cnf(c_0_91,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_88]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])])).

cnf(c_0_92,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_93,plain,(
    ! [X34,X35,X36] :
      ( ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ l1_pre_topc(X35)
      | ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))
      | ~ v3_tops_2(X36,X34,X35)
      | v3_tops_2(k2_tops_2(u1_struct_0(X34),u1_struct_0(X35),X36),X35,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_tops_2])])])])).

cnf(c_0_94,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_90]),c_0_91]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk4_0)
    | k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk5_0)
    | ~ v2_funct_1(esk6_0)
    | ~ v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_96,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_88]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])])).

cnf(c_0_97,plain,
    ( v2_struct_0(X2)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v3_tops_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_28]),c_0_32])])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_88])]),c_0_96]),c_0_90]),c_0_91])])).

cnf(c_0_100,plain,
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

cnf(c_0_101,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_88]),c_0_18]),c_0_19]),c_0_20]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_102,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_28]),c_0_29])])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk4_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_99]),c_0_29])])).

cnf(c_0_104,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0)) != k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0))
    | k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk4_0)
    | k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk5_0)
    | ~ v2_funct_1(esk6_0)
    | ~ v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_105,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,X1)) = k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_47]),c_0_46]),c_0_48]),c_0_49]),c_0_50]),c_0_32]),c_0_29])]),c_0_21])).

cnf(c_0_106,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk7_0) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,esk7_0)) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0)) != k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_88])]),c_0_96]),c_0_90]),c_0_91])])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_99]),c_0_106]),c_0_107]),c_0_108]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.47  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.031 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t74_tops_2, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4))=k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_2)).
% 0.19/0.47  fof(t62_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 0.19/0.47  fof(t63_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_tops_2)).
% 0.19/0.47  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.47  fof(t67_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tops_2)).
% 0.19/0.47  fof(dt_k2_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v1_funct_1(k2_tops_2(X1,X2,X3))&v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1))&m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 0.19/0.47  fof(t73_tops_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4))=k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tops_2)).
% 0.19/0.47  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.19/0.47  fof(d5_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>((((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))&v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_2)).
% 0.19/0.47  fof(t57_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tops_2)).
% 0.19/0.47  fof(t56_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_2)).
% 0.19/0.47  fof(t70_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)=>v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_tops_2)).
% 0.19/0.47  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4))=k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))))))))), inference(assume_negation,[status(cth)],[t74_tops_2])).
% 0.19/0.47  fof(c_0_13, plain, ![X24, X25, X26]:((k1_relset_1(u1_struct_0(X25),u1_struct_0(X24),k2_tops_2(u1_struct_0(X24),u1_struct_0(X25),X26))=k2_struct_0(X25)|(k2_relset_1(u1_struct_0(X24),u1_struct_0(X25),X26)!=k2_struct_0(X25)|~v2_funct_1(X26))|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25)))))|(v2_struct_0(X25)|~l1_struct_0(X25))|~l1_struct_0(X24))&(k2_relset_1(u1_struct_0(X25),u1_struct_0(X24),k2_tops_2(u1_struct_0(X24),u1_struct_0(X25),X26))=k2_struct_0(X24)|(k2_relset_1(u1_struct_0(X24),u1_struct_0(X25),X26)!=k2_struct_0(X25)|~v2_funct_1(X26))|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25)))))|(v2_struct_0(X25)|~l1_struct_0(X25))|~l1_struct_0(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).
% 0.19/0.47  fof(c_0_14, negated_conjecture, ![X46]:((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))))&(((m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))|(k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk4_0)|k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk5_0)|~v2_funct_1(esk6_0))|~v3_tops_2(esk6_0,esk4_0,esk5_0))&(k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0))!=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0))|(k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk4_0)|k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk5_0)|~v2_funct_1(esk6_0))|~v3_tops_2(esk6_0,esk4_0,esk5_0)))&((((k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0))&(k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)))&(v2_funct_1(esk6_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)))&(~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(esk4_0)))|k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,X46))=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X46))|v3_tops_2(esk6_0,esk4_0,esk5_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).
% 0.19/0.47  fof(c_0_15, plain, ![X27, X28, X29]:(~l1_struct_0(X27)|(~l1_struct_0(X28)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))|(k2_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29)!=k2_struct_0(X28)|~v2_funct_1(X29)|v2_funct_1(k2_tops_2(u1_struct_0(X27),u1_struct_0(X28),X29)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_tops_2])])])).
% 0.19/0.47  cnf(c_0_16, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X1)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_17, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_18, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_22, negated_conjecture, (v2_funct_1(esk6_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  fof(c_0_23, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.47  cnf(c_0_24, plain, (v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_25, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X2)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  fof(c_0_26, plain, ![X30, X31, X32, X33]:(~l1_struct_0(X30)|(~l1_struct_0(X31)|(~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))|(k2_relset_1(u1_struct_0(X30),u1_struct_0(X31),X32)!=k2_struct_0(X31)|~v2_funct_1(X32)|k7_relset_1(u1_struct_0(X30),u1_struct_0(X31),X32,X33)=k8_relset_1(u1_struct_0(X31),u1_struct_0(X30),k2_tops_2(u1_struct_0(X30),u1_struct_0(X31),X32),X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).
% 0.19/0.47  cnf(c_0_27, negated_conjecture, (k1_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))=k2_struct_0(esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.19/0.47  cnf(c_0_28, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  fof(c_0_30, plain, ![X11, X12, X13]:(((v1_funct_1(k2_tops_2(X11,X12,X13))|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))&(v1_funct_2(k2_tops_2(X11,X12,X13),X12,X11)|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))))&(m1_subset_1(k2_tops_2(X11,X12,X13),k1_zfmisc_1(k2_zfmisc_1(X12,X11)))|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).
% 0.19/0.47  cnf(c_0_31, negated_conjecture, (v2_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))|v3_tops_2(esk6_0,esk4_0,esk5_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_22])).
% 0.19/0.47  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_33, negated_conjecture, (k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))=k2_struct_0(esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.19/0.47  cnf(c_0_34, plain, (k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  fof(c_0_35, plain, ![X37, X38, X39, X40]:(((((k1_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39)=k2_struct_0(X37)|~v3_tops_2(X39,X37,X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38)))))|(~v2_pre_topc(X38)|~l1_pre_topc(X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(k2_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39)=k2_struct_0(X38)|~v3_tops_2(X39,X37,X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38)))))|(~v2_pre_topc(X38)|~l1_pre_topc(X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37))))&(v2_funct_1(X39)|~v3_tops_2(X39,X37,X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38)))))|(~v2_pre_topc(X38)|~l1_pre_topc(X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37))))&(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,k2_pre_topc(X38,X40))=k2_pre_topc(X37,k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,X40))|~v3_tops_2(X39,X37,X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38)))))|(~v2_pre_topc(X38)|~l1_pre_topc(X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37))))&((m1_subset_1(esk3_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X38)))|(k1_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39)!=k2_struct_0(X37)|k2_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39)!=k2_struct_0(X38)|~v2_funct_1(X39))|v3_tops_2(X39,X37,X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38)))))|(~v2_pre_topc(X38)|~l1_pre_topc(X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,k2_pre_topc(X38,esk3_3(X37,X38,X39)))!=k2_pre_topc(X37,k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,esk3_3(X37,X38,X39)))|(k1_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39)!=k2_struct_0(X37)|k2_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39)!=k2_struct_0(X38)|~v2_funct_1(X39))|v3_tops_2(X39,X37,X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38)))))|(~v2_pre_topc(X38)|~l1_pre_topc(X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t73_tops_2])])])])])])).
% 0.19/0.47  cnf(c_0_36, negated_conjecture, (k1_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))=k2_struct_0(esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)|~l1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.19/0.47  cnf(c_0_37, plain, (v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_38, plain, (v1_funct_1(k2_tops_2(X1,X2,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_39, plain, (m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_40, negated_conjecture, (v2_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))|v3_tops_2(esk6_0,esk4_0,esk5_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_32])])).
% 0.19/0.47  cnf(c_0_41, negated_conjecture, (k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))=k2_struct_0(esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)|~l1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_28]), c_0_29])])).
% 0.19/0.47  cnf(c_0_42, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|v3_tops_2(esk6_0,esk4_0,esk5_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_22])).
% 0.19/0.47  fof(c_0_43, plain, ![X5, X6]:(~l1_pre_topc(X5)|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|m1_subset_1(k2_pre_topc(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.19/0.47  cnf(c_0_44, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v3_tops_2(X3,X1,X2)|v2_struct_0(X1)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.47  cnf(c_0_45, negated_conjecture, (k1_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))=k2_struct_0(esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_32])])).
% 0.19/0.47  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_47, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_48, negated_conjecture, (v1_funct_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.47  cnf(c_0_49, negated_conjecture, (v1_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_18]), c_0_19])]), c_0_20])])).
% 0.19/0.47  cnf(c_0_50, negated_conjecture, (m1_subset_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.47  cnf(c_0_51, negated_conjecture, (v2_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_28]), c_0_29])])).
% 0.19/0.47  cnf(c_0_52, negated_conjecture, (k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))=k2_struct_0(esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_32])])).
% 0.19/0.47  cnf(c_0_53, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|v3_tops_2(esk6_0,esk4_0,esk5_0)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_28]), c_0_32])])).
% 0.19/0.47  cnf(c_0_54, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.47  cnf(c_0_55, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)|m1_subset_1(esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_29]), c_0_32])]), c_0_21]), c_0_51]), c_0_52])).
% 0.19/0.47  cnf(c_0_56, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|v3_tops_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_28]), c_0_29])])).
% 0.19/0.47  cnf(c_0_57, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)|m1_subset_1(k2_pre_topc(esk4_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_29])])).
% 0.19/0.47  cnf(c_0_58, plain, (v3_tops_2(X3,X1,X2)|v2_struct_0(X1)|k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk3_3(X1,X2,X3)))!=k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3)))|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.47  cnf(c_0_59, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))|v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.47  cnf(c_0_60, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,X1))=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1))|v3_tops_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  fof(c_0_61, plain, ![X8, X9, X10]:((((((k1_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10)=k2_struct_0(X8)|~v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8))&(k2_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10)=k2_struct_0(X9)|~v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8)))&(v2_funct_1(X10)|~v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8)))&(v5_pre_topc(X10,X8,X9)|~v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8)))&(v5_pre_topc(k2_tops_2(u1_struct_0(X8),u1_struct_0(X9),X10),X9,X8)|~v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8)))&(k1_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10)!=k2_struct_0(X8)|k2_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10)!=k2_struct_0(X9)|~v2_funct_1(X10)|~v5_pre_topc(X10,X8,X9)|~v5_pre_topc(k2_tops_2(u1_struct_0(X8),u1_struct_0(X9),X10),X9,X8)|v3_tops_2(X10,X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))))|~l1_pre_topc(X9)|~l1_pre_topc(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).
% 0.19/0.47  cnf(c_0_62, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)|k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))!=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_29]), c_0_32])]), c_0_21]), c_0_51]), c_0_52]), c_0_45])).
% 0.19/0.47  cnf(c_0_63, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))|v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_55])).
% 0.19/0.47  cnf(c_0_64, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk3_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))|v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_55])).
% 0.19/0.47  fof(c_0_65, plain, ![X19, X20, X21, X22]:((~v5_pre_topc(X21,X19,X20)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|r1_tarski(k7_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,k2_pre_topc(X19,X22)),k2_pre_topc(X20,k7_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,X22))))|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((m1_subset_1(esk2_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))|v5_pre_topc(X21,X19,X20)|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r1_tarski(k7_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,k2_pre_topc(X19,esk2_3(X19,X20,X21))),k2_pre_topc(X20,k7_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,esk2_3(X19,X20,X21))))|v5_pre_topc(X21,X19,X20)|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|(~v2_pre_topc(X19)|~l1_pre_topc(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tops_2])])])])])])).
% 0.19/0.47  fof(c_0_66, plain, ![X14, X15, X16, X17]:((~v5_pre_topc(X16,X14,X15)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|r1_tarski(k2_pre_topc(X14,k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,X17)),k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,k2_pre_topc(X15,X17))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|(~v2_pre_topc(X15)|~l1_pre_topc(X15))|(~v2_pre_topc(X14)|~l1_pre_topc(X14)))&((m1_subset_1(esk1_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X15)))|v5_pre_topc(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|(~v2_pre_topc(X15)|~l1_pre_topc(X15))|(~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r1_tarski(k2_pre_topc(X14,k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,esk1_3(X14,X15,X16))),k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,k2_pre_topc(X15,esk1_3(X14,X15,X16))))|v5_pre_topc(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|(~v2_pre_topc(X15)|~l1_pre_topc(X15))|(~v2_pre_topc(X14)|~l1_pre_topc(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).
% 0.19/0.47  cnf(c_0_67, plain, (v5_pre_topc(X1,X2,X3)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.47  cnf(c_0_68, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.19/0.47  cnf(c_0_69, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.47  cnf(c_0_70, plain, (r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4)),k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,k2_pre_topc(X3,X4)))|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.47  cnf(c_0_71, negated_conjecture, (v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_48]), c_0_49]), c_0_50]), c_0_29]), c_0_32])])).
% 0.19/0.47  cnf(c_0_72, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_18]), c_0_47]), c_0_46]), c_0_19]), c_0_20]), c_0_32]), c_0_29])]), c_0_21])).
% 0.19/0.47  cnf(c_0_73, negated_conjecture, (r1_tarski(k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)),k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,X1)))|v3_tops_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_29]), c_0_32])])).
% 0.19/0.47  cnf(c_0_74, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|m1_subset_1(k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_72]), c_0_29])])).
% 0.19/0.47  cnf(c_0_75, negated_conjecture, (r1_tarski(k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk2_3(esk4_0,esk5_0,esk6_0))),k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0))))|v5_pre_topc(esk6_0,esk4_0,esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_73, c_0_72])).
% 0.19/0.47  cnf(c_0_76, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0)))=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0)))|v5_pre_topc(esk6_0,esk4_0,esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_74])).
% 0.19/0.47  cnf(c_0_77, negated_conjecture, (r1_tarski(k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk2_3(esk4_0,esk5_0,esk6_0))),k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0))))|v5_pre_topc(esk6_0,esk4_0,esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.47  cnf(c_0_78, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk2_3(esk4_0,esk5_0,esk6_0))=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0))|v5_pre_topc(esk6_0,esk4_0,esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_72])).
% 0.19/0.47  cnf(c_0_79, plain, (v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|~r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,esk2_3(X1,X2,X3))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.47  cnf(c_0_80, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0)))=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0)))|v5_pre_topc(esk6_0,esk4_0,esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_72])).
% 0.19/0.47  cnf(c_0_81, plain, (v3_tops_2(X3,X1,X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v5_pre_topc(X3,X1,X2)|~v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.47  cnf(c_0_82, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0))),k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0))))|v5_pre_topc(esk6_0,esk4_0,esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.47  cnf(c_0_84, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)|~r1_tarski(k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0))),k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_47]), c_0_46]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])]), c_0_21])).
% 0.19/0.47  cnf(c_0_85, negated_conjecture, (v3_tops_2(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)|~v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])]), c_0_22]), c_0_17])).
% 0.19/0.47  cnf(c_0_86, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_80]), c_0_84])).
% 0.19/0.47  cnf(c_0_87, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.47  cnf(c_0_88, negated_conjecture, (v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_71])).
% 0.19/0.47  cnf(c_0_89, plain, (v2_funct_1(X1)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.47  cnf(c_0_90, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])])).
% 0.19/0.47  cnf(c_0_91, negated_conjecture, (v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_88]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])])).
% 0.19/0.47  cnf(c_0_92, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.47  fof(c_0_93, plain, ![X34, X35, X36]:(~l1_pre_topc(X34)|(v2_struct_0(X35)|~l1_pre_topc(X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))|(~v3_tops_2(X36,X34,X35)|v3_tops_2(k2_tops_2(u1_struct_0(X34),u1_struct_0(X35),X36),X35,X34))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_tops_2])])])])).
% 0.19/0.47  cnf(c_0_94, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|~l1_struct_0(esk5_0)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_90]), c_0_91]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.47  cnf(c_0_95, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))|k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk4_0)|k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk5_0)|~v2_funct_1(esk6_0)|~v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_96, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_88]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])])).
% 0.19/0.47  cnf(c_0_97, plain, (v2_struct_0(X2)|v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v3_tops_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.19/0.47  cnf(c_0_98, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_28]), c_0_32])])).
% 0.19/0.47  cnf(c_0_99, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_88])]), c_0_96]), c_0_90]), c_0_91])])).
% 0.19/0.47  cnf(c_0_100, plain, (k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k2_pre_topc(X2,X1))=k2_pre_topc(X3,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,X1))|v2_struct_0(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_tops_2(X4,X3,X2)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.47  cnf(c_0_101, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_88]), c_0_18]), c_0_19]), c_0_20]), c_0_32]), c_0_29])]), c_0_21])).
% 0.19/0.47  cnf(c_0_102, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_28]), c_0_29])])).
% 0.19/0.47  cnf(c_0_103, negated_conjecture, (m1_subset_1(k2_pre_topc(esk4_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_99]), c_0_29])])).
% 0.19/0.47  cnf(c_0_104, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0))!=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0))|k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk4_0)|k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk5_0)|~v2_funct_1(esk6_0)|~v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_105, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,X1))=k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_47]), c_0_46]), c_0_48]), c_0_49]), c_0_50]), c_0_32]), c_0_29])]), c_0_21])).
% 0.19/0.47  cnf(c_0_106, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk7_0)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_102, c_0_99])).
% 0.19/0.47  cnf(c_0_107, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,esk7_0))=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.19/0.47  cnf(c_0_108, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0))!=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_88])]), c_0_96]), c_0_90]), c_0_91])])).
% 0.19/0.47  cnf(c_0_109, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_99]), c_0_106]), c_0_107]), c_0_108]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 110
% 0.19/0.47  # Proof object clause steps            : 85
% 0.19/0.47  # Proof object formula steps           : 25
% 0.19/0.47  # Proof object conjectures             : 67
% 0.19/0.47  # Proof object clause conjectures      : 64
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 35
% 0.19/0.47  # Proof object initial formulas used   : 12
% 0.19/0.47  # Proof object generating inferences   : 48
% 0.19/0.47  # Proof object simplifying inferences  : 177
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 12
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 42
% 0.19/0.47  # Removed in clause preprocessing      : 0
% 0.19/0.47  # Initial clauses in saturation        : 42
% 0.19/0.47  # Processed clauses                    : 475
% 0.19/0.47  # ...of these trivial                  : 1
% 0.19/0.47  # ...subsumed                          : 48
% 0.19/0.47  # ...remaining for further processing  : 425
% 0.19/0.47  # Other redundant clauses eliminated   : 0
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 119
% 0.19/0.47  # Backward-rewritten                   : 172
% 0.19/0.47  # Generated clauses                    : 1228
% 0.19/0.47  # ...of the previous two non-trivial   : 1221
% 0.19/0.47  # Contextual simplify-reflections      : 30
% 0.19/0.47  # Paramodulations                      : 1228
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 0
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 95
% 0.19/0.47  #    Positive orientable unit clauses  : 55
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 2
% 0.19/0.47  #    Non-unit-clauses                  : 38
% 0.19/0.47  # Current number of unprocessed clauses: 94
% 0.19/0.47  # ...number of literals in the above   : 186
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 330
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 21821
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 7719
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 197
% 0.19/0.47  # Unit Clause-clause subsumption calls : 779
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 180
% 0.19/0.47  # BW rewrite match successes           : 7
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 108348
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.126 s
% 0.19/0.47  # System time              : 0.004 s
% 0.19/0.47  # Total time               : 0.130 s
% 0.19/0.47  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
