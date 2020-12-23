%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1795+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:46 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  142 (8436 expanded)
%              Number of clauses        :  103 (2700 expanded)
%              Number of leaves         :   19 (2102 expanded)
%              Depth                    :   19
%              Number of atoms          :  635 (63534 expanded)
%              Number of equality atoms :   45 (1378 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t111_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_xboole_0(u1_struct_0(X3),X2)
               => ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
                  & v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
                  & v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
                  & m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_tmap_1)).

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

fof(dt_k5_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k5_tmap_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_tmap_1)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t109_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_xboole_0(u1_struct_0(X3),X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t49_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( v5_pre_topc(X3,X2,X1)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => r1_tmap_1(X2,X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( r1_xboole_0(u1_struct_0(X3),X2)
                 => ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
                    & v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
                    & v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
                    & m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t111_tmap_1])).

fof(c_0_20,plain,(
    ! [X14,X15] :
      ( v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | k6_tmap_1(X14,X15) = g1_pre_topc(u1_struct_0(X14),k5_tmap_1(X14,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & r1_xboole_0(u1_struct_0(esk4_0),esk3_0)
    & ( ~ v1_funct_1(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0))
      | ~ v1_funct_2(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
      | ~ v5_pre_topc(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k6_tmap_1(esk2_0,esk3_0))
      | ~ m1_subset_1(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | m1_subset_1(k5_tmap_1(X24,X25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_tmap_1])])])).

fof(c_0_23,plain,(
    ! [X36,X37,X38,X39] :
      ( ( X36 = X38
        | g1_pre_topc(X36,X37) != g1_pre_topc(X38,X39)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k1_zfmisc_1(X36))) )
      & ( X37 = X39
        | g1_pre_topc(X36,X37) != g1_pre_topc(X38,X39)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k1_zfmisc_1(X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_tmap_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X27,X28] :
      ( ( v1_pre_topc(k6_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( v2_pre_topc(k6_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( l1_pre_topc(k6_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,esk3_0)) = k6_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k5_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

fof(c_0_34,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_35,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_pre_topc(X1,X2) != k6_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_38,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_41,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X10,X11,X12,X13] :
      ( v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
      | ~ m1_pre_topc(X13,X10)
      | k2_tmap_1(X10,X11,X12,X13) = k2_partfun1(u1_struct_0(X10),u1_struct_0(X11),X12,u1_struct_0(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_43,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
      | k7_tmap_1(X8,X9) = k6_partfun1(u1_struct_0(X8)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

fof(c_0_44,plain,(
    ! [X29,X30] :
      ( ( v1_funct_1(k7_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( v1_funct_2(k7_tmap_1(X29,X30),u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,X30)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( m1_subset_1(k7_tmap_1(X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,X30)))))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38])]),c_0_39]),c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_48,plain,(
    ! [X26] :
      ( v1_partfun1(k6_partfun1(X26),X26)
      & m1_subset_1(k6_partfun1(X26),k1_zfmisc_1(k2_zfmisc_1(X26,X26))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1)) = k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_45]),c_0_46]),c_0_40])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k5_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_45]),c_0_46]),c_0_40])])).

cnf(c_0_54,negated_conjecture,
    ( k2_tmap_1(X1,k6_tmap_1(esk2_0,esk3_0),X2,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,u1_struct_0(X3))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_46]),c_0_40])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_25]),c_0_45]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_59,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_60,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)) = k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_25])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k5_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_25])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | l1_pre_topc(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_45]),c_0_46]),c_0_40])])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | v1_pre_topc(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_45]),c_0_46]),c_0_40])])).

fof(c_0_64,plain,(
    ! [X20,X21,X22,X23] :
      ( ( v1_funct_1(k2_tmap_1(X20,X21,X22,X23))
        | ~ l1_struct_0(X20)
        | ~ l1_struct_0(X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_struct_0(X23) )
      & ( v1_funct_2(k2_tmap_1(X20,X21,X22,X23),u1_struct_0(X23),u1_struct_0(X21))
        | ~ l1_struct_0(X20)
        | ~ l1_struct_0(X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_struct_0(X23) )
      & ( m1_subset_1(k2_tmap_1(X20,X21,X22,X23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))
        | ~ l1_struct_0(X20)
        | ~ l1_struct_0(X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_struct_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_65,negated_conjecture,
    ( k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),X1) = k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_56]),c_0_56]),c_0_57]),c_0_56]),c_0_58]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_67,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X32)
      | l1_pre_topc(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1)))))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_45]),c_0_46]),c_0_40])])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0) != g1_pre_topc(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_60]),c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | l1_pre_topc(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_25])).

cnf(c_0_71,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | v1_pre_topc(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_25])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1)))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_45]),c_0_46]),c_0_40])])).

fof(c_0_73,plain,(
    ! [X44,X45,X46,X47] :
      ( v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
      | v2_struct_0(X46)
      | ~ m1_pre_topc(X46,X44)
      | ~ r1_xboole_0(u1_struct_0(X46),X45)
      | ~ m1_subset_1(X47,u1_struct_0(X46))
      | r1_tmap_1(X46,k6_tmap_1(X44,X45),k2_tmap_1(X44,k6_tmap_1(X44,X45),k7_tmap_1(X44,X45),X46),X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t109_tmap_1])])])])).

cnf(c_0_74,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0) = k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_77,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | l1_struct_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_78,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)))))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_25])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)) = u1_struct_0(esk2_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_38])]),c_0_70]),c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_45]),c_0_46]),c_0_40])])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0)))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_25])).

cnf(c_0_83,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_84,plain,(
    ! [X48,X49,X50,X51] :
      ( ( ~ v5_pre_topc(X50,X49,X48)
        | ~ m1_subset_1(X51,u1_struct_0(X49))
        | r1_tmap_1(X49,X48,X50,X51)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,u1_struct_0(X49),u1_struct_0(X48))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X48))))
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( m1_subset_1(esk1_3(X48,X49,X50),u1_struct_0(X49))
        | v5_pre_topc(X50,X49,X48)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,u1_struct_0(X49),u1_struct_0(X48))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X48))))
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( ~ r1_tmap_1(X49,X48,X50,esk1_3(X48,X49,X50))
        | v5_pre_topc(X50,X49,X48)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,u1_struct_0(X49),u1_struct_0(X48))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X48))))
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ r1_xboole_0(u1_struct_0(X3),X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_86,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | v2_pre_topc(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_45]),c_0_45]),c_0_57]),c_0_58]),c_0_45]),c_0_76])])).

cnf(c_0_88,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_66]),c_0_27])])).

fof(c_0_90,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ v1_funct_1(X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k2_partfun1(X40,X41,X42,X43) = k7_relat_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_25])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_80])).

cnf(c_0_94,negated_conjecture,
    ( v1_funct_2(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_75]),c_0_45]),c_0_45]),c_0_57]),c_0_58]),c_0_45]),c_0_76])])).

cnf(c_0_95,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_96,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,esk1_3(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_97,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_98,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_99,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_100,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])])).

cnf(c_0_102,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_103,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_76]),c_0_57]),c_0_58]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_104,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(X1)) = k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),X1)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_91]),c_0_26]),c_0_27])]),c_0_28]),c_0_92]),c_0_93])).

cnf(c_0_105,negated_conjecture,
    ( k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),X1) = k7_tmap_1(esk2_0,esk3_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_45]),c_0_56]),c_0_46]),c_0_40])])).

cnf(c_0_106,negated_conjecture,
    ( v1_funct_2(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_88]),c_0_89])])).

cnf(c_0_107,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_75]),c_0_45]),c_0_57]),c_0_58]),c_0_45]),c_0_76])])).

cnf(c_0_108,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),esk1_3(X2,X4,k2_tmap_1(X1,X2,X3,X4)))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_74]),c_0_95]),c_0_83]),c_0_88]),c_0_88])).

cnf(c_0_109,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_66])]),c_0_99])).

cnf(c_0_110,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_66]),c_0_26]),c_0_27])])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_88]),c_0_27])])).

cnf(c_0_112,negated_conjecture,
    ( k7_relat_1(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_58]),c_0_76])])).

fof(c_0_113,plain,(
    ! [X16,X17,X18,X19] :
      ( ( v1_funct_1(k2_partfun1(X16,X17,X18,X19))
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( m1_subset_1(k2_partfun1(X16,X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_114,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk4_0)) = k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0),esk4_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_66])).

cnf(c_0_115,negated_conjecture,
    ( k7_tmap_1(k6_tmap_1(esk2_0,esk3_0),esk3_0) = k7_tmap_1(esk2_0,esk3_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_25])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_2(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_88]),c_0_27])])).

cnf(c_0_117,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_88]),c_0_89])])).

cnf(c_0_118,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k6_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),esk4_0,k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_45]),c_0_57]),c_0_58]),c_0_45]),c_0_76]),c_0_46]),c_0_110]),c_0_40]),c_0_89])]),c_0_99])).

cnf(c_0_119,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X2))
    | v5_pre_topc(X3,X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_88]),c_0_40])])).

cnf(c_0_121,negated_conjecture,
    ( k2_partfun1(X1,X2,k7_tmap_1(esk2_0,esk3_0),u1_struct_0(X3)) = k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(esk2_0,esk3_0),X3)
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_pre_topc(X3,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_112]),c_0_58])])).

cnf(c_0_122,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_123,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)) = k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(esk2_0,esk3_0),esk4_0)
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_124,negated_conjecture,
    ( v1_funct_2(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_88]),c_0_40])])).

cnf(c_0_125,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
    | ~ v5_pre_topc(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_126,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_88]),c_0_27])])).

cnf(c_0_127,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k6_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),esk4_0,k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_88]),c_0_27])])).

cnf(c_0_128,negated_conjecture,
    ( v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),X2,X1),u1_struct_0(X2))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_45]),c_0_46]),c_0_40])])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_76]),c_0_66])])).

cnf(c_0_130,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(esk2_0,esk3_0),esk4_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_58]),c_0_76])])).

cnf(c_0_131,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_121]),c_0_76]),c_0_66])])).

cnf(c_0_132,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_45]),c_0_45])).

cnf(c_0_133,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_88]),c_0_40])])).

cnf(c_0_134,negated_conjecture,
    ( v5_pre_topc(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),esk4_0,k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0))),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_75])).

cnf(c_0_135,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),esk4_0,k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk4_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_110]),c_0_89])]),c_0_99]),c_0_130]),c_0_131])).

fof(c_0_136,plain,(
    ! [X34,X35] :
      ( ( ~ v2_struct_0(k6_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) )
      & ( v1_pre_topc(k6_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) )
      & ( v2_pre_topc(k6_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_137,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ v5_pre_topc(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_75]),c_0_120]),c_0_133]),c_0_124])).

cnf(c_0_138,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,esk2_0,k7_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k6_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_121]),c_0_76]),c_0_66])]),c_0_135])).

cnf(c_0_139,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_136])).

cnf(c_0_140,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_121]),c_0_76]),c_0_66])]),c_0_138])).

cnf(c_0_141,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),
    [proof]).

%------------------------------------------------------------------------------
