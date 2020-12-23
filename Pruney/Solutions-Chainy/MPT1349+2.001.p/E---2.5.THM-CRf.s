%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:06 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 (18282 expanded)
%              Number of clauses        :   69 (5596 expanded)
%              Number of leaves         :   13 (4532 expanded)
%              Depth                    :   17
%              Number of atoms          :  586 (235542 expanded)
%              Number of equality atoms :   78 (52820 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   67 (   3 average)
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

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

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

fof(d12_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( v4_pre_topc(X4,X2)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

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

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

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

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ v5_pre_topc(X29,X27,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X27)))
        | r1_tarski(k7_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29,k2_pre_topc(X27,X30)),k2_pre_topc(X28,k7_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29,X30)))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk2_3(X27,X28,X29),k1_zfmisc_1(u1_struct_0(X27)))
        | v5_pre_topc(X29,X27,X28)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r1_tarski(k7_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29,k2_pre_topc(X27,esk2_3(X27,X28,X29))),k2_pre_topc(X28,k7_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29,esk2_3(X27,X28,X29))))
        | v5_pre_topc(X29,X27,X28)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tops_2])])])])])])).

fof(c_0_15,negated_conjecture,(
    ! [X48] :
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
      & ( ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,X48)) = k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X48))
        | v3_tops_2(esk6_0,esk4_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).

cnf(c_0_16,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_26,plain,(
    ! [X24,X25,X26] :
      ( ( v1_funct_1(k2_tops_2(X24,X25,X26))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( v1_funct_2(k2_tops_2(X24,X25,X26),X25,X24)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( m1_subset_1(k2_tops_2(X24,X25,X26),k1_zfmisc_1(k2_zfmisc_1(X25,X24)))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

cnf(c_0_27,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,X1)) = k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1))
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ l1_struct_0(X32)
      | ~ l1_struct_0(X33)
      | ~ v1_funct_1(X34)
      | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X32)))
      | k2_relset_1(u1_struct_0(X32),u1_struct_0(X33),X34) != k2_struct_0(X33)
      | ~ v2_funct_1(X34)
      | k7_relset_1(u1_struct_0(X32),u1_struct_0(X33),X34,X35) = k8_relset_1(u1_struct_0(X33),u1_struct_0(X32),k2_tops_2(u1_struct_0(X32),u1_struct_0(X33),X34),X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).

fof(c_0_31,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ v5_pre_topc(X13,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v4_pre_topc(X14,X12)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X11),u1_struct_0(X12),X13,X14),X11)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
        | ~ l1_pre_topc(X12)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk1_3(X11,X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v5_pre_topc(X13,X11,X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
        | ~ l1_pre_topc(X12)
        | ~ l1_pre_topc(X11) )
      & ( v4_pre_topc(esk1_3(X11,X12,X13),X12)
        | v5_pre_topc(X13,X11,X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
        | ~ l1_pre_topc(X12)
        | ~ l1_pre_topc(X11) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X11),u1_struct_0(X12),X13,esk1_3(X11,X12,X13)),X11)
        | v5_pre_topc(X13,X11,X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
        | ~ l1_pre_topc(X12)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_32,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_funct_1(k2_tops_2(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X21,X22,X23] :
      ( ( k1_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23) = k2_struct_0(X21)
        | ~ v3_tops_2(X23,X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( k2_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23) = k2_struct_0(X22)
        | ~ v3_tops_2(X23,X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( v2_funct_1(X23)
        | ~ v3_tops_2(X23,X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( v5_pre_topc(X23,X21,X22)
        | ~ v3_tops_2(X23,X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X21),u1_struct_0(X22),X23),X22,X21)
        | ~ v3_tops_2(X23,X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( k1_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23) != k2_struct_0(X21)
        | k2_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23) != k2_struct_0(X22)
        | ~ v2_funct_1(X23)
        | ~ v5_pre_topc(X23,X21,X22)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X21),u1_struct_0(X22),X23),X22,X21)
        | v3_tops_2(X23,X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

cnf(c_0_36,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0))) = k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0)))
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_struct_0(esk5_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( v2_funct_1(esk6_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_42,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_20]),c_0_23])])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_17]),c_0_20]),c_0_23])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_20]),c_0_23])])).

cnf(c_0_47,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_struct_0(esk4_0)
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( v3_tops_2(esk6_0,esk4_0,esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_18]),c_0_19]),c_0_17]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_38])]),c_0_24])).

fof(c_0_50,plain,(
    ! [X19,X20] :
      ( ( ~ v4_pre_topc(X20,X19)
        | k2_pre_topc(X19,X20) = X20
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ v2_pre_topc(X19)
        | k2_pre_topc(X19,X20) != X20
        | v4_pre_topc(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_51,plain,
    ( v4_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_17]),c_0_20]),c_0_23])]),c_0_41])).

cnf(c_0_53,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)
    | m1_subset_1(esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_22]),c_0_21]),c_0_46])])).

cnf(c_0_55,negated_conjecture,
    ( v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_17]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_49]),c_0_41]),c_0_40])).

cnf(c_0_56,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)),esk4_0)
    | v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_44]),c_0_45]),c_0_22]),c_0_21]),c_0_46])])).

fof(c_0_58,plain,(
    ! [X7,X8,X9,X10] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | m1_subset_1(k7_relset_1(X7,X8,X9,X10),k1_zfmisc_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_59,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_21])])).

cnf(c_0_60,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))) = k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_54]),c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))) = esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))
    | v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_22])]),c_0_54])).

cnf(c_0_62,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | v3_tops_2(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_53]),c_0_22])])).

cnf(c_0_64,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_23])).

cnf(c_0_67,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_68,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))
    | v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_54]),c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( v3_tops_2(esk6_0,esk4_0,esk5_0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_18]),c_0_21]),c_0_66])])).

cnf(c_0_70,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_71,negated_conjecture,
    ( v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_44]),c_0_45]),c_0_22]),c_0_21]),c_0_46])]),c_0_69]),c_0_55])).

cnf(c_0_72,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_73,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_17]),c_0_20]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_74,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_71]),c_0_17]),c_0_20]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_75,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_76,plain,(
    ! [X36,X37,X38] :
      ( ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ l1_pre_topc(X37)
      | ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
      | ~ v3_tops_2(X38,X36,X37)
      | v3_tops_2(k2_tops_2(u1_struct_0(X36),u1_struct_0(X37),X38),X37,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_tops_2])])])])).

cnf(c_0_77,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_73]),c_0_74]),c_0_17]),c_0_20]),c_0_23])])).

fof(c_0_78,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | m1_subset_1(k2_pre_topc(X16,X17),k1_zfmisc_1(u1_struct_0(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk4_0)
    | k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk5_0)
    | ~ v2_funct_1(esk6_0)
    | ~ v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_80,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_71]),c_0_17]),c_0_20]),c_0_21]),c_0_22]),c_0_23])])).

fof(c_0_81,plain,(
    ! [X39,X40,X41,X42] :
      ( ( k1_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41) = k2_struct_0(X39)
        | ~ v3_tops_2(X41,X39,X40)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( k2_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41) = k2_struct_0(X40)
        | ~ v3_tops_2(X41,X39,X40)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v2_funct_1(X41)
        | ~ v3_tops_2(X41,X39,X40)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))
        | k8_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41,k2_pre_topc(X40,X42)) = k2_pre_topc(X39,k8_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41,X42))
        | ~ v3_tops_2(X41,X39,X40)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( m1_subset_1(esk3_3(X39,X40,X41),k1_zfmisc_1(u1_struct_0(X40)))
        | k1_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41) != k2_struct_0(X39)
        | k2_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41) != k2_struct_0(X40)
        | ~ v2_funct_1(X41)
        | v3_tops_2(X41,X39,X40)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( k8_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41,k2_pre_topc(X40,esk3_3(X39,X40,X41))) != k2_pre_topc(X39,k8_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41,esk3_3(X39,X40,X41)))
        | k1_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41) != k2_struct_0(X39)
        | k2_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41) != k2_struct_0(X40)
        | ~ v2_funct_1(X41)
        | v3_tops_2(X41,X39,X40)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t73_tops_2])])])])])])).

cnf(c_0_82,plain,
    ( v2_struct_0(X2)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v3_tops_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_53]),c_0_21])])).

cnf(c_0_84,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_71])]),c_0_80]),c_0_73]),c_0_74])])).

cnf(c_0_86,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_71]),c_0_17]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_88,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_53]),c_0_22])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk4_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_22])])).

cnf(c_0_90,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0)) != k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0))
    | k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk4_0)
    | k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) != k2_struct_0(esk5_0)
    | ~ v2_funct_1(esk6_0)
    | ~ v3_tops_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_91,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,X1)) = k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_18]),c_0_19]),c_0_44]),c_0_45]),c_0_21]),c_0_22]),c_0_46])]),c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk7_0) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,esk7_0)) = k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0)) != k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_71])]),c_0_80]),c_0_73]),c_0_74])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_85]),c_0_92]),c_0_93]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.48  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.48  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.48  #
% 0.20/0.48  # Preprocessing time       : 0.032 s
% 0.20/0.48  # Presaturation interreduction done
% 0.20/0.48  
% 0.20/0.48  # Proof found!
% 0.20/0.48  # SZS status Theorem
% 0.20/0.48  # SZS output start CNFRefutation
% 0.20/0.48  fof(t74_tops_2, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4))=k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_2)).
% 0.20/0.48  fof(t57_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_2)).
% 0.20/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.48  fof(dt_k2_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v1_funct_1(k2_tops_2(X1,X2,X3))&v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1))&m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 0.20/0.48  fof(t67_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tops_2)).
% 0.20/0.48  fof(d12_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X4,X2)=>v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 0.20/0.48  fof(d5_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>((((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))&v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 0.20/0.48  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.48  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.48  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.20/0.48  fof(t70_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)=>v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_tops_2)).
% 0.20/0.48  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.20/0.48  fof(t73_tops_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4))=k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_2)).
% 0.20/0.48  fof(c_0_13, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,X4))=k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))))))))), inference(assume_negation,[status(cth)],[t74_tops_2])).
% 0.20/0.48  fof(c_0_14, plain, ![X27, X28, X29, X30]:((~v5_pre_topc(X29,X27,X28)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X27)))|r1_tarski(k7_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29,k2_pre_topc(X27,X30)),k2_pre_topc(X28,k7_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29,X30))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&((m1_subset_1(esk2_3(X27,X28,X29),k1_zfmisc_1(u1_struct_0(X27)))|v5_pre_topc(X29,X27,X28)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~r1_tarski(k7_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29,k2_pre_topc(X27,esk2_3(X27,X28,X29))),k2_pre_topc(X28,k7_relset_1(u1_struct_0(X27),u1_struct_0(X28),X29,esk2_3(X27,X28,X29))))|v5_pre_topc(X29,X27,X28)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|(~v2_pre_topc(X27)|~l1_pre_topc(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tops_2])])])])])])).
% 0.20/0.48  fof(c_0_15, negated_conjecture, ![X48]:((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))))&(((m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))|(k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk4_0)|k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk5_0)|~v2_funct_1(esk6_0))|~v3_tops_2(esk6_0,esk4_0,esk5_0))&(k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0))!=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0))|(k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk4_0)|k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk5_0)|~v2_funct_1(esk6_0))|~v3_tops_2(esk6_0,esk4_0,esk5_0)))&((((k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0))&(k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)))&(v2_funct_1(esk6_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)))&(~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(esk4_0)))|k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,X48))=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X48))|v3_tops_2(esk6_0,esk4_0,esk5_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).
% 0.20/0.48  cnf(c_0_16, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.48  cnf(c_0_17, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  fof(c_0_25, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.48  fof(c_0_26, plain, ![X24, X25, X26]:(((v1_funct_1(k2_tops_2(X24,X25,X26))|(~v1_funct_1(X26)|~v1_funct_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))&(v1_funct_2(k2_tops_2(X24,X25,X26),X25,X24)|(~v1_funct_1(X26)|~v1_funct_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))))&(m1_subset_1(k2_tops_2(X24,X25,X26),k1_zfmisc_1(k2_zfmisc_1(X25,X24)))|(~v1_funct_1(X26)|~v1_funct_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).
% 0.20/0.48  cnf(c_0_27, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,X1))=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1))|v3_tops_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_28, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.20/0.48  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.48  fof(c_0_30, plain, ![X32, X33, X34, X35]:(~l1_struct_0(X32)|(~l1_struct_0(X33)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X32)))|(k2_relset_1(u1_struct_0(X32),u1_struct_0(X33),X34)!=k2_struct_0(X33)|~v2_funct_1(X34)|k7_relset_1(u1_struct_0(X32),u1_struct_0(X33),X34,X35)=k8_relset_1(u1_struct_0(X33),u1_struct_0(X32),k2_tops_2(u1_struct_0(X32),u1_struct_0(X33),X34),X35)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).
% 0.20/0.48  fof(c_0_31, plain, ![X11, X12, X13, X14]:((~v5_pre_topc(X13,X11,X12)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(~v4_pre_topc(X14,X12)|v4_pre_topc(k8_relset_1(u1_struct_0(X11),u1_struct_0(X12),X13,X14),X11)))|(~v1_funct_1(X13)|~v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12)))))|~l1_pre_topc(X12)|~l1_pre_topc(X11))&((m1_subset_1(esk1_3(X11,X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|v5_pre_topc(X13,X11,X12)|(~v1_funct_1(X13)|~v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12)))))|~l1_pre_topc(X12)|~l1_pre_topc(X11))&((v4_pre_topc(esk1_3(X11,X12,X13),X12)|v5_pre_topc(X13,X11,X12)|(~v1_funct_1(X13)|~v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12)))))|~l1_pre_topc(X12)|~l1_pre_topc(X11))&(~v4_pre_topc(k8_relset_1(u1_struct_0(X11),u1_struct_0(X12),X13,esk1_3(X11,X12,X13)),X11)|v5_pre_topc(X13,X11,X12)|(~v1_funct_1(X13)|~v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12)))))|~l1_pre_topc(X12)|~l1_pre_topc(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).
% 0.20/0.48  cnf(c_0_32, plain, (v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.48  cnf(c_0_33, plain, (v1_funct_1(k2_tops_2(X1,X2,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.48  cnf(c_0_34, plain, (m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.48  fof(c_0_35, plain, ![X21, X22, X23]:((((((k1_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23)=k2_struct_0(X21)|~v3_tops_2(X23,X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22)))))|~l1_pre_topc(X22)|~l1_pre_topc(X21))&(k2_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23)=k2_struct_0(X22)|~v3_tops_2(X23,X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22)))))|~l1_pre_topc(X22)|~l1_pre_topc(X21)))&(v2_funct_1(X23)|~v3_tops_2(X23,X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22)))))|~l1_pre_topc(X22)|~l1_pre_topc(X21)))&(v5_pre_topc(X23,X21,X22)|~v3_tops_2(X23,X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22)))))|~l1_pre_topc(X22)|~l1_pre_topc(X21)))&(v5_pre_topc(k2_tops_2(u1_struct_0(X21),u1_struct_0(X22),X23),X22,X21)|~v3_tops_2(X23,X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22)))))|~l1_pre_topc(X22)|~l1_pre_topc(X21)))&(k1_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23)!=k2_struct_0(X21)|k2_relset_1(u1_struct_0(X21),u1_struct_0(X22),X23)!=k2_struct_0(X22)|~v2_funct_1(X23)|~v5_pre_topc(X23,X21,X22)|~v5_pre_topc(k2_tops_2(u1_struct_0(X21),u1_struct_0(X22),X23),X22,X21)|v3_tops_2(X23,X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22)))))|~l1_pre_topc(X22)|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).
% 0.20/0.48  cnf(c_0_36, plain, (v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|~r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X1,esk2_3(X1,X2,X3))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.48  cnf(c_0_37, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0)))=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk2_3(esk4_0,esk5_0,esk6_0)))|v3_tops_2(esk6_0,esk4_0,esk5_0)|v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.48  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 0.20/0.48  cnf(c_0_39, plain, (k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.48  cnf(c_0_40, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk5_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_41, negated_conjecture, (v2_funct_1(esk6_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  fof(c_0_42, plain, ![X18]:(~l1_pre_topc(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.48  cnf(c_0_43, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.48  cnf(c_0_44, negated_conjecture, (v1_funct_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_17]), c_0_20]), c_0_23])])).
% 0.20/0.48  cnf(c_0_45, negated_conjecture, (v1_funct_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_17]), c_0_20]), c_0_23])])).
% 0.20/0.48  cnf(c_0_46, negated_conjecture, (m1_subset_1(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_17]), c_0_20]), c_0_23])])).
% 0.20/0.48  cnf(c_0_47, plain, (v3_tops_2(X3,X1,X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v5_pre_topc(X3,X1,X2)|~v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.48  cnf(c_0_48, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk4_0)|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_49, negated_conjecture, (v3_tops_2(esk6_0,esk4_0,esk5_0)|v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_18]), c_0_19]), c_0_17]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_38])]), c_0_24])).
% 0.20/0.48  fof(c_0_50, plain, ![X19, X20]:((~v4_pre_topc(X20,X19)|k2_pre_topc(X19,X20)=X20|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(~v2_pre_topc(X19)|k2_pre_topc(X19,X20)!=X20|v4_pre_topc(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.48  cnf(c_0_51, plain, (v4_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.48  cnf(c_0_52, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|v3_tops_2(esk6_0,esk4_0,esk5_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_17]), c_0_20]), c_0_23])]), c_0_41])).
% 0.20/0.48  cnf(c_0_53, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.48  cnf(c_0_54, negated_conjecture, (v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)|m1_subset_1(esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_22]), c_0_21]), c_0_46])])).
% 0.20/0.48  cnf(c_0_55, negated_conjecture, (v3_tops_2(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_17]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_49]), c_0_41]), c_0_40])).
% 0.20/0.48  cnf(c_0_56, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.48  cnf(c_0_57, negated_conjecture, (v4_pre_topc(esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)),esk4_0)|v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_44]), c_0_45]), c_0_22]), c_0_21]), c_0_46])])).
% 0.20/0.48  fof(c_0_58, plain, ![X7, X8, X9, X10]:(~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|m1_subset_1(k7_relset_1(X7,X8,X9,X10),k1_zfmisc_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.20/0.48  cnf(c_0_59, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|v3_tops_2(esk6_0,esk4_0,esk5_0)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_21])])).
% 0.20/0.48  cnf(c_0_60, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_54]), c_0_55])).
% 0.20/0.48  cnf(c_0_61, negated_conjecture, (k2_pre_topc(esk4_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))=esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))|v5_pre_topc(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_22])]), c_0_54])).
% 0.20/0.48  cnf(c_0_62, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.48  cnf(c_0_63, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|v3_tops_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_53]), c_0_22])])).
% 0.20/0.48  cnf(c_0_64, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|k2_pre_topc(X1,X2)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.48  cnf(c_0_65, negated_conjecture, (k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))))=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_55])).
% 0.20/0.48  cnf(c_0_66, negated_conjecture, (m1_subset_1(k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_62, c_0_23])).
% 0.20/0.48  cnf(c_0_67, plain, (v5_pre_topc(X3,X1,X2)|~v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.48  cnf(c_0_68, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)))|v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_54]), c_0_55])).
% 0.20/0.48  cnf(c_0_69, negated_conjecture, (v3_tops_2(esk6_0,esk4_0,esk5_0)|v4_pre_topc(k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk1_3(esk5_0,esk4_0,k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0))),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_18]), c_0_21]), c_0_66])])).
% 0.20/0.48  cnf(c_0_70, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.48  cnf(c_0_71, negated_conjecture, (v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_44]), c_0_45]), c_0_22]), c_0_21]), c_0_46])]), c_0_69]), c_0_55])).
% 0.20/0.48  cnf(c_0_72, plain, (v2_funct_1(X1)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.48  cnf(c_0_73, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_17]), c_0_20]), c_0_21]), c_0_22]), c_0_23])])).
% 0.20/0.48  cnf(c_0_74, negated_conjecture, (v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_71]), c_0_17]), c_0_20]), c_0_21]), c_0_22]), c_0_23])])).
% 0.20/0.48  cnf(c_0_75, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.48  fof(c_0_76, plain, ![X36, X37, X38]:(~l1_pre_topc(X36)|(v2_struct_0(X37)|~l1_pre_topc(X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))|(~v3_tops_2(X38,X36,X37)|v3_tops_2(k2_tops_2(u1_struct_0(X36),u1_struct_0(X37),X38),X37,X36))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_tops_2])])])])).
% 0.20/0.48  cnf(c_0_77, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|~l1_struct_0(esk5_0)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_73]), c_0_74]), c_0_17]), c_0_20]), c_0_23])])).
% 0.20/0.48  fof(c_0_78, plain, ![X16, X17]:(~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|m1_subset_1(k2_pre_topc(X16,X17),k1_zfmisc_1(u1_struct_0(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.20/0.48  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))|k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk4_0)|k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk5_0)|~v2_funct_1(esk6_0)|~v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_80, negated_conjecture, (k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_71]), c_0_17]), c_0_20]), c_0_21]), c_0_22]), c_0_23])])).
% 0.20/0.48  fof(c_0_81, plain, ![X39, X40, X41, X42]:(((((k1_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41)=k2_struct_0(X39)|~v3_tops_2(X41,X39,X40)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(k2_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41)=k2_struct_0(X40)|~v3_tops_2(X41,X39,X40)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(v2_funct_1(X41)|~v3_tops_2(X41,X39,X40)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))|k8_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41,k2_pre_topc(X40,X42))=k2_pre_topc(X39,k8_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41,X42))|~v3_tops_2(X41,X39,X40)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&((m1_subset_1(esk3_3(X39,X40,X41),k1_zfmisc_1(u1_struct_0(X40)))|(k1_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41)!=k2_struct_0(X39)|k2_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41)!=k2_struct_0(X40)|~v2_funct_1(X41))|v3_tops_2(X41,X39,X40)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(k8_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41,k2_pre_topc(X40,esk3_3(X39,X40,X41)))!=k2_pre_topc(X39,k8_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41,esk3_3(X39,X40,X41)))|(k1_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41)!=k2_struct_0(X39)|k2_relset_1(u1_struct_0(X39),u1_struct_0(X40),X41)!=k2_struct_0(X40)|~v2_funct_1(X41))|v3_tops_2(X41,X39,X40)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t73_tops_2])])])])])])).
% 0.20/0.48  cnf(c_0_82, plain, (v2_struct_0(X2)|v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v3_tops_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.48  cnf(c_0_83, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_53]), c_0_21])])).
% 0.20/0.48  cnf(c_0_84, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.48  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_71])]), c_0_80]), c_0_73]), c_0_74])])).
% 0.20/0.48  cnf(c_0_86, plain, (k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k2_pre_topc(X2,X1))=k2_pre_topc(X3,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,X1))|v2_struct_0(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_tops_2(X4,X3,X2)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.48  cnf(c_0_87, negated_conjecture, (v3_tops_2(k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_71]), c_0_17]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.20/0.48  cnf(c_0_88, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_53]), c_0_22])])).
% 0.20/0.48  cnf(c_0_89, negated_conjecture, (m1_subset_1(k2_pre_topc(esk4_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_22])])).
% 0.20/0.48  cnf(c_0_90, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0))!=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0))|k1_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk4_0)|k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)!=k2_struct_0(esk5_0)|~v2_funct_1(esk6_0)|~v3_tops_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_91, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,X1))=k2_pre_topc(esk5_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_18]), c_0_19]), c_0_44]), c_0_45]), c_0_21]), c_0_22]), c_0_46])]), c_0_24])).
% 0.20/0.48  cnf(c_0_92, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),esk7_0)=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_88, c_0_85])).
% 0.20/0.48  cnf(c_0_93, negated_conjecture, (k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),k2_tops_2(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0),k2_pre_topc(esk4_0,esk7_0))=k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.20/0.48  cnf(c_0_94, negated_conjecture, (k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk4_0,esk7_0))!=k2_pre_topc(esk5_0,k7_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_71])]), c_0_80]), c_0_73]), c_0_74])])).
% 0.20/0.48  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_85]), c_0_92]), c_0_93]), c_0_94]), ['proof']).
% 0.20/0.48  # SZS output end CNFRefutation
% 0.20/0.48  # Proof object total steps             : 96
% 0.20/0.48  # Proof object clause steps            : 69
% 0.20/0.48  # Proof object formula steps           : 27
% 0.20/0.48  # Proof object conjectures             : 50
% 0.20/0.48  # Proof object clause conjectures      : 47
% 0.20/0.48  # Proof object formula conjectures     : 3
% 0.20/0.48  # Proof object initial clauses used    : 35
% 0.20/0.48  # Proof object initial formulas used   : 13
% 0.20/0.48  # Proof object generating inferences   : 31
% 0.20/0.48  # Proof object simplifying inferences  : 134
% 0.20/0.48  # Training examples: 0 positive, 0 negative
% 0.20/0.48  # Parsed axioms                        : 13
% 0.20/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.48  # Initial clauses                      : 46
% 0.20/0.48  # Removed in clause preprocessing      : 0
% 0.20/0.48  # Initial clauses in saturation        : 46
% 0.20/0.48  # Processed clauses                    : 683
% 0.20/0.48  # ...of these trivial                  : 9
% 0.20/0.48  # ...subsumed                          : 173
% 0.20/0.48  # ...remaining for further processing  : 500
% 0.20/0.48  # Other redundant clauses eliminated   : 2
% 0.20/0.48  # Clauses deleted for lack of memory   : 0
% 0.20/0.48  # Backward-subsumed                    : 16
% 0.20/0.48  # Backward-rewritten                   : 264
% 0.20/0.48  # Generated clauses                    : 1701
% 0.20/0.48  # ...of the previous two non-trivial   : 1238
% 0.20/0.48  # Contextual simplify-reflections      : 26
% 0.20/0.48  # Paramodulations                      : 1699
% 0.20/0.48  # Factorizations                       : 0
% 0.20/0.48  # Equation resolutions                 : 2
% 0.20/0.48  # Propositional unsat checks           : 0
% 0.20/0.48  #    Propositional check models        : 0
% 0.20/0.48  #    Propositional check unsatisfiable : 0
% 0.20/0.48  #    Propositional clauses             : 0
% 0.20/0.48  #    Propositional clauses after purity: 0
% 0.20/0.48  #    Propositional unsat core size     : 0
% 0.20/0.48  #    Propositional preprocessing time  : 0.000
% 0.20/0.48  #    Propositional encoding time       : 0.000
% 0.20/0.48  #    Propositional solver time         : 0.000
% 0.20/0.48  #    Success case prop preproc time    : 0.000
% 0.20/0.48  #    Success case prop encoding time   : 0.000
% 0.20/0.48  #    Success case prop solver time     : 0.000
% 0.20/0.48  # Current number of processed clauses  : 176
% 0.20/0.48  #    Positive orientable unit clauses  : 134
% 0.20/0.48  #    Positive unorientable unit clauses: 0
% 0.20/0.48  #    Negative unit clauses             : 3
% 0.20/0.48  #    Non-unit-clauses                  : 39
% 0.20/0.48  # Current number of unprocessed clauses: 548
% 0.20/0.48  # ...number of literals in the above   : 1102
% 0.20/0.48  # Current number of archived formulas  : 0
% 0.20/0.48  # Current number of archived clauses   : 322
% 0.20/0.48  # Clause-clause subsumption calls (NU) : 22188
% 0.20/0.48  # Rec. Clause-clause subsumption calls : 9387
% 0.20/0.48  # Non-unit clause-clause subsumptions  : 215
% 0.20/0.48  # Unit Clause-clause subsumption calls : 2007
% 0.20/0.48  # Rewrite failures with RHS unbound    : 0
% 0.20/0.48  # BW rewrite match attempts            : 4906
% 0.20/0.48  # BW rewrite match successes           : 5
% 0.20/0.48  # Condensation attempts                : 0
% 0.20/0.48  # Condensation successes               : 0
% 0.20/0.48  # Termbank termtop insertions          : 126626
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.135 s
% 0.20/0.48  # System time              : 0.009 s
% 0.20/0.48  # Total time               : 0.144 s
% 0.20/0.48  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
