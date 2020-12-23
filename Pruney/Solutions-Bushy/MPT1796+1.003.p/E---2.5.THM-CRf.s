%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1796+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:46 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  203 (14361 expanded)
%              Number of clauses        :  170 (4867 expanded)
%              Number of leaves         :   16 (3503 expanded)
%              Depth                    :   44
%              Number of atoms          :  922 (106865 expanded)
%              Number of equality atoms :  141 (11343 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   34 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t112_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( u1_struct_0(X3) = X2
               => ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
                  & v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
                  & v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
                  & m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_tmap_1)).

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

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

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

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(t110_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( u1_struct_0(X3) = X2
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tmap_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( u1_struct_0(X3) = X2
                 => ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
                    & v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
                    & v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
                    & m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t112_tmap_1])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk4_0)
    & u1_struct_0(esk6_0) = esk5_0
    & ( ~ v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0))
      | ~ v1_funct_2(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),u1_struct_0(esk6_0),u1_struct_0(k6_tmap_1(esk4_0,esk5_0)))
      | ~ v5_pre_topc(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),esk6_0,k6_tmap_1(esk4_0,esk5_0))
      | ~ m1_subset_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_18,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | m1_subset_1(k5_tmap_1(X22,X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_tmap_1])])])).

fof(c_0_19,plain,(
    ! [X37,X38,X39,X40] :
      ( ( X37 = X39
        | g1_pre_topc(X37,X38) != g1_pre_topc(X39,X40)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k1_zfmisc_1(X37))) )
      & ( X38 = X40
        | g1_pre_topc(X37,X38) != g1_pre_topc(X39,X40)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k1_zfmisc_1(X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_tmap_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k5_tmap_1(esk4_0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

fof(c_0_26,plain,(
    ! [X16,X17] :
      ( v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | k6_tmap_1(X16,X17) = g1_pre_topc(u1_struct_0(X16),k5_tmap_1(X16,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X2)) != g1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | k6_tmap_1(esk4_0,X2) != g1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_31,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | g1_pre_topc(X1,X2) != k6_tmap_1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_34,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33])])).

fof(c_0_36,plain,(
    ! [X35,X36] :
      ( ( ~ v2_struct_0(k6_tmap_1(X35,X36))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) )
      & ( v1_pre_topc(k6_tmap_1(X35,X36))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) )
      & ( v2_pre_topc(k6_tmap_1(X35,X36))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_37,negated_conjecture,
    ( k5_tmap_1(esk4_0,X1) = X2
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1)) != g1_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(k6_tmap_1(esk4_0,esk5_0))) = k6_tmap_1(esk4_0,esk5_0)
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_35])).

fof(c_0_39,plain,(
    ! [X24,X25] :
      ( ( v1_pre_topc(k6_tmap_1(X24,X25))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( v2_pre_topc(k6_tmap_1(X24,X25))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( l1_pre_topc(k6_tmap_1(X24,X25))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k5_tmap_1(esk4_0,X1) = u1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1)) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_45,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k5_tmap_1(esk4_0,X1) = X2
    | k6_tmap_1(esk4_0,X1) != g1_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_28]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( k5_tmap_1(esk4_0,X1) = u1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1)) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_43]),c_0_22]),c_0_23])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))
    | ~ v2_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_45]),c_0_22]),c_0_23])])).

cnf(c_0_51,negated_conjecture,
    ( k5_tmap_1(esk4_0,esk5_0) = X1
    | g1_pre_topc(X2,X1) != k6_tmap_1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( k5_tmap_1(esk4_0,X1) = u1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1)) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_30])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_30])])).

cnf(c_0_54,negated_conjecture,
    ( k5_tmap_1(esk4_0,esk5_0) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | k6_tmap_1(X1,X2) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) = k5_tmap_1(esk4_0,esk5_0)
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,esk5_0)) != k6_tmap_1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_30])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_48]),c_0_30])])).

cnf(c_0_57,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1))) = k5_tmap_1(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33])])).

cnf(c_0_58,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(X1,X2)) = k6_tmap_1(esk4_0,esk5_0)
    | v2_struct_0(X1)
    | k6_tmap_1(X1,X2) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_54]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) = k5_tmap_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_28]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,esk5_0)) = X1
    | g1_pre_topc(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)),k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X2)) != g1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k5_tmap_1(esk4_0,esk5_0) = k5_tmap_1(esk4_0,X1)
    | k6_tmap_1(esk4_0,X1) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,esk5_0)) = X1
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X2) != g1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))
    | ~ v2_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_28]),c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,esk5_0)) = k6_tmap_1(esk4_0,X1)
    | k6_tmap_1(esk4_0,X1) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_61]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,esk5_0)) = X1
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X2) != g1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_50]),c_0_30])])).

fof(c_0_65,plain,(
    ! [X26,X27] :
      ( ( v1_funct_1(k7_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( v1_funct_2(k7_tmap_1(X26,X27),u1_struct_0(X26),u1_struct_0(k6_tmap_1(X26,X27)))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( m1_subset_1(k7_tmap_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(k6_tmap_1(X26,X27)))))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

fof(c_0_66,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
      | k7_tmap_1(X8,X9) = k6_partfun1(u1_struct_0(X8)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

cnf(c_0_67,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,esk5_0)) = k6_tmap_1(esk4_0,X1)
    | k6_tmap_1(esk4_0,X1) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_68,negated_conjecture,
    ( k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1) = X2
    | g1_pre_topc(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)),k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1)) != g1_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,esk5_0)) = X1
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X2) != g1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_48]),c_0_30])])).

cnf(c_0_70,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1))) = u1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_33])])).

cnf(c_0_73,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,esk5_0)) = k6_tmap_1(esk4_0,X1)
    | k6_tmap_1(esk4_0,X1) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_48]),c_0_30])])).

cnf(c_0_74,negated_conjecture,
    ( k5_tmap_1(esk4_0,X1) = k5_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1)) != k6_tmap_1(X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_75,negated_conjecture,
    ( k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1) = X2
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1) != g1_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))
    | ~ v2_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_28]),c_0_44])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X2) != g1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_35])).

cnf(c_0_77,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,X1)) = u1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_28]),c_0_22]),c_0_23])]),c_0_20]),c_0_48])).

cnf(c_0_79,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,esk5_0)) = k6_tmap_1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_30])).

cnf(c_0_80,negated_conjecture,
    ( k5_tmap_1(esk4_0,X1) = k5_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | k6_tmap_1(esk4_0,X1) != k6_tmap_1(esk4_0,esk5_0)
    | k6_tmap_1(esk4_0,esk5_0) != k6_tmap_1(X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_58]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_81,negated_conjecture,
    ( k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1) = X2
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1) != g1_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_50]),c_0_30])])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X2) != g1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_1(k6_partfun1(u1_struct_0(esk4_0)))
    | v2_struct_0(k6_tmap_1(esk4_0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_48]),c_0_50])).

cnf(c_0_84,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk4_0,X1)) = k5_tmap_1(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_22]),c_0_23])]),c_0_20]),c_0_48])).

cnf(c_0_85,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,X1)) = k6_tmap_1(esk4_0,esk5_0)
    | k6_tmap_1(esk4_0,X1) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_86,negated_conjecture,
    ( k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1) = X2
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1) != g1_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_48]),c_0_30])])).

cnf(c_0_87,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X2) != g1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_48]),c_0_30])])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_1(k6_partfun1(u1_struct_0(esk4_0)))
    | v2_struct_0(k6_tmap_1(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_30])).

cnf(c_0_89,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(esk4_0,X1)),k5_tmap_1(esk4_0,X1)) = k6_tmap_1(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_84]),c_0_48])).

cnf(c_0_90,negated_conjecture,
    ( k5_tmap_1(esk4_0,esk5_0) = k5_tmap_1(esk4_0,X1)
    | k6_tmap_1(esk4_0,X1) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1) = X2
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1) != g1_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_78]),c_0_30])])).

cnf(c_0_92,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0) != g1_pre_topc(X1,X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_30])).

fof(c_0_93,plain,(
    ! [X18,X19,X20,X21] :
      ( ( v1_funct_1(k2_tmap_1(X18,X19,X20,X21))
        | ~ l1_struct_0(X18)
        | ~ l1_struct_0(X19)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X19))))
        | ~ l1_struct_0(X21) )
      & ( v1_funct_2(k2_tmap_1(X18,X19,X20,X21),u1_struct_0(X21),u1_struct_0(X19))
        | ~ l1_struct_0(X18)
        | ~ l1_struct_0(X19)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X19))))
        | ~ l1_struct_0(X21) )
      & ( m1_subset_1(k2_tmap_1(X18,X19,X20,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X19))))
        | ~ l1_struct_0(X18)
        | ~ l1_struct_0(X19)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X19))))
        | ~ l1_struct_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_94,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_1(k6_partfun1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_30]),c_0_44])).

cnf(c_0_96,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)),k5_tmap_1(esk4_0,X1)) = k6_tmap_1(esk4_0,esk5_0)
    | k6_tmap_1(esk4_0,X1) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_30])])).

cnf(c_0_97,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_98,negated_conjecture,
    ( k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1) = X2
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1) != g1_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_99,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) = u1_struct_0(esk4_0)
    | ~ v1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_33])])).

cnf(c_0_100,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_94]),c_0_22]),c_0_23])])).

fof(c_0_102,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_1(k6_partfun1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_104,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | k6_tmap_1(esk4_0,X1) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_78]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_106,negated_conjecture,
    ( k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0) = X1
    | k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0) != g1_pre_topc(X2,X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_30])).

cnf(c_0_107,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0))) = k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)
    | ~ v1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,X1),k7_tmap_1(esk4_0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(esk4_0,X1)))))
    | ~ l1_struct_0(k6_tmap_1(esk4_0,X1))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_2(k7_tmap_1(esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)))
    | ~ v1_funct_1(k7_tmap_1(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_109,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_71]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_111,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | k6_tmap_1(esk4_0,X1) != k6_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_112,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_30])).

cnf(c_0_113,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) = k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)
    | ~ v1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,X1),k7_tmap_1(esk4_0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(esk4_0,X1)))))
    | ~ l1_struct_0(k6_tmap_1(esk4_0,X1))
    | ~ l1_struct_0(X2)
    | ~ v1_funct_2(k7_tmap_1(esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_23])]),c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,esk5_0)) = u1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_30])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_117,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)),k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) = k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)
    | ~ v1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_113])).

cnf(c_0_118,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))
    | ~ v2_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_119,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ l1_struct_0(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_116]),c_0_30])])).

cnf(c_0_121,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) = u1_struct_0(k6_tmap_1(esk4_0,esk5_0))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)),k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1)) != k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))
    | ~ v1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_117])).

cnf(c_0_122,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_50]),c_0_30])])).

cnf(c_0_123,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(esk4_0,esk5_0),X2,X3))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_35]),c_0_109])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_35]),c_0_30])])).

cnf(c_0_125,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_109])).

fof(c_0_126,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X29)
      | l1_pre_topc(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_127,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | v2_pre_topc(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_128,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) = u1_struct_0(k6_tmap_1(esk4_0,esk5_0))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(esk4_0,esk5_0)),k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1)) != k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))
    | ~ v2_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_42]),c_0_44]),c_0_122])).

cnf(c_0_129,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(esk4_0,esk5_0),X2,X3))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_130,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

fof(c_0_131,plain,(
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

cnf(c_0_132,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0))
    | ~ v1_funct_2(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),u1_struct_0(esk6_0),u1_struct_0(k6_tmap_1(esk4_0,esk5_0)))
    | ~ v5_pre_topc(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),esk6_0,k6_tmap_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_133,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_134,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_48]),c_0_30])])).

cnf(c_0_135,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_136,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_137,plain,(
    ! [X45,X46,X47,X48] :
      ( ( ~ v5_pre_topc(X47,X46,X45)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | r1_tmap_1(X46,X45,X47,X48)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( m1_subset_1(esk3_3(X45,X46,X47),u1_struct_0(X46))
        | v5_pre_topc(X47,X46,X45)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( ~ r1_tmap_1(X46,X45,X47,esk3_3(X45,X46,X47))
        | v5_pre_topc(X47,X46,X45)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

cnf(c_0_138,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_127])).

fof(c_0_139,plain,(
    ! [X41,X42,X43,X44] :
      ( v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | v2_struct_0(X43)
      | ~ m1_pre_topc(X43,X41)
      | u1_struct_0(X43) != X42
      | ~ m1_subset_1(X44,u1_struct_0(X43))
      | r1_tmap_1(X43,k6_tmap_1(X41,X42),k2_tmap_1(X41,k6_tmap_1(X41,X42),k7_tmap_1(X41,X42),X43),X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t110_tmap_1])])])])).

cnf(c_0_140,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) = u1_struct_0(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1)) != k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_78]),c_0_30])])).

cnf(c_0_141,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(esk4_0,esk5_0),X2,X3))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_48]),c_0_30])])).

cnf(c_0_142,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_48]),c_0_30])])).

cnf(c_0_143,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_144,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),esk6_0,k6_tmap_1(esk4_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),esk5_0,u1_struct_0(k6_tmap_1(esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0))
    | ~ m1_subset_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,u1_struct_0(k6_tmap_1(esk4_0,esk5_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_133]),c_0_133])).

cnf(c_0_145,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,u1_struct_0(esk4_0))))
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_133])).

cnf(c_0_146,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_23])])).

cnf(c_0_147,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,esk3_3(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_148,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_136]),c_0_22]),c_0_23])])).

cnf(c_0_149,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_150,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | u1_struct_0(X3) != X2
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_139])).

cnf(c_0_151,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) = u1_struct_0(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1)) != k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_50]),c_0_30])])).

cnf(c_0_152,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),X1))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(k7_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_116])])).

cnf(c_0_153,negated_conjecture,
    ( k2_tmap_1(X1,k6_tmap_1(esk4_0,X2),X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(esk4_0),X3,u1_struct_0(X4))
    | v2_struct_0(k6_tmap_1(esk4_0,X2))
    | v2_struct_0(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_pre_topc(X4,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_78]),c_0_48]),c_0_50])).

cnf(c_0_154,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),esk6_0,k6_tmap_1(esk4_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),esk5_0,u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0))
    | ~ m1_subset_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_144,c_0_115]),c_0_115])).

cnf(c_0_155,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_109]),c_0_146])])).

cnf(c_0_156,negated_conjecture,
    ( v5_pre_topc(X1,esk6_0,X2)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(esk6_0,X2,X1,esk3_3(X2,esk6_0,X1))
    | ~ v1_funct_2(X1,esk5_0,u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_133]),c_0_148]),c_0_146])]),c_0_149])).

cnf(c_0_157,plain,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X1)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X1)),k7_tmap_1(X2,u1_struct_0(X1)),X1),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_150])).

cnf(c_0_158,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) = u1_struct_0(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1)) != k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_159,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,esk5_0),u1_struct_0(X1)))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(k7_tmap_1(esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_116]),c_0_142]),c_0_30]),c_0_22]),c_0_23])]),c_0_44]),c_0_20])).

cnf(c_0_160,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),esk6_0,k6_tmap_1(esk4_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),esk5_0,u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154,c_0_155])])).

cnf(c_0_161,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,esk5_0),k7_tmap_1(X1,esk5_0),esk6_0),esk6_0,k6_tmap_1(X1,esk5_0))
    | v2_struct_0(X1)
    | ~ v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,esk5_0),k7_tmap_1(X1,esk5_0),esk6_0),esk5_0,u1_struct_0(k6_tmap_1(X1,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,esk5_0),k7_tmap_1(X1,esk5_0),esk6_0))
    | ~ m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,esk5_0),k7_tmap_1(X1,esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,u1_struct_0(k6_tmap_1(X1,esk5_0)))))
    | ~ m1_subset_1(esk3_3(k6_tmap_1(X1,esk5_0),esk6_0,k2_tmap_1(X1,k6_tmap_1(X1,esk5_0),k7_tmap_1(X1,esk5_0),esk6_0)),esk5_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_157]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_149]),c_0_43]),c_0_45]),c_0_40])).

cnf(c_0_162,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) = u1_struct_0(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),X1)) != k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_48]),c_0_30])])).

cnf(c_0_163,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,esk5_0),u1_struct_0(X1)))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_70]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_164,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
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
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_165,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),esk5_0,u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0))
    | ~ m1_subset_1(esk3_3(k6_tmap_1(esk4_0,esk5_0),esk6_0,k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_115]),c_0_115]),c_0_155]),c_0_30]),c_0_136]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_166,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) = u1_struct_0(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) != k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_162,c_0_30])).

cnf(c_0_167,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(k6_tmap_1(esk4_0,X1),X2)) = k6_tmap_1(k6_tmap_1(esk4_0,X1),X2)
    | v2_struct_0(k6_tmap_1(esk4_0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_78]),c_0_48]),c_0_50])).

cnf(c_0_168,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,esk5_0),u1_struct_0(X1)))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_169,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0),esk5_0,u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk5_0),esk6_0))
    | ~ v2_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_164]),c_0_133]),c_0_133]),c_0_115]),c_0_133]),c_0_115]),c_0_155]),c_0_148]),c_0_146])]),c_0_149]),c_0_44]),c_0_165])).

cnf(c_0_170,plain,
    ( k7_tmap_1(X1,X2) = k7_tmap_1(X1,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_71])).

cnf(c_0_171,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k6_tmap_1(esk4_0,X1),X2),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(k6_tmap_1(esk4_0,X1),X2)))
    | v2_struct_0(k6_tmap_1(esk4_0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_78]),c_0_48]),c_0_50])).

cnf(c_0_172,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0)) = u1_struct_0(esk4_0)
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_167]),c_0_30])]),c_0_44])).

cnf(c_0_173,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,esk5_0),u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_109]),c_0_23])])).

cnf(c_0_174,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1),esk6_0),esk5_0,u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1),esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_170]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_175,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_172]),c_0_30])]),c_0_44])).

cnf(c_0_176,negated_conjecture,
    ( m1_subset_1(k6_partfun1(u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_71]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_177,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,esk4_0,k7_tmap_1(esk4_0,esk5_0),X1))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(k7_tmap_1(esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_143]),c_0_116]),c_0_142]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_178,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1),esk6_0),esk5_0,u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1),esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_50]),c_0_30])])).

cnf(c_0_179,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k6_tmap_1(esk4_0,esk5_0),esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_180,negated_conjecture,
    ( k7_tmap_1(k6_tmap_1(esk4_0,X1),X2) = k6_partfun1(u1_struct_0(esk4_0))
    | v2_struct_0(k6_tmap_1(esk4_0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_78]),c_0_48]),c_0_50])).

cnf(c_0_181,negated_conjecture,
    ( m1_subset_1(k6_partfun1(u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_35]),c_0_30])])).

cnf(c_0_182,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,esk4_0,k7_tmap_1(esk4_0,esk5_0),X1))
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_70]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_183,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1),esk6_0),esk5_0,u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1),esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_48]),c_0_30])])).

cnf(c_0_184,negated_conjecture,
    ( v1_funct_2(k6_partfun1(u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_180]),c_0_30])]),c_0_44])).

cnf(c_0_185,negated_conjecture,
    ( m1_subset_1(k6_partfun1(u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_186,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,esk4_0,k7_tmap_1(esk4_0,X1),X2))
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_pre_topc(X2,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_170]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_187,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k6_partfun1(u1_struct_0(esk4_0)),esk6_0),esk5_0,u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,k6_tmap_1(esk4_0,esk5_0),k6_partfun1(u1_struct_0(esk4_0)),esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_71]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_188,negated_conjecture,
    ( v1_funct_2(k6_partfun1(u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_189,negated_conjecture,
    ( m1_subset_1(k6_partfun1(u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_48]),c_0_30])])).

cnf(c_0_190,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,esk4_0,k6_partfun1(u1_struct_0(esk4_0)),X1))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_71]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_191,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk4_0),k6_partfun1(u1_struct_0(esk4_0)),esk5_0),esk5_0,u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk4_0),k6_partfun1(u1_struct_0(esk4_0)),esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_153]),c_0_133]),c_0_133]),c_0_188]),c_0_103]),c_0_189]),c_0_30]),c_0_136]),c_0_22]),c_0_23])]),c_0_44]),c_0_20])).

cnf(c_0_192,negated_conjecture,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,esk5_0) = k2_tmap_1(X1,X2,X3,esk6_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_143,c_0_133])).

cnf(c_0_193,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_194,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,esk4_0,k6_partfun1(u1_struct_0(esk4_0)),X1))
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_190,c_0_30])).

cnf(c_0_195,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk4_0,esk4_0,k6_partfun1(u1_struct_0(esk4_0)),esk6_0),esk5_0,u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,esk4_0,k6_partfun1(u1_struct_0(esk4_0)),esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_192]),c_0_188]),c_0_103]),c_0_189]),c_0_136]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_196,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,esk6_0),esk5_0,u1_struct_0(X2))
    | ~ l1_struct_0(esk6_0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(spm,[status(thm)],[c_0_193,c_0_133])).

cnf(c_0_197,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,esk4_0,k6_partfun1(u1_struct_0(esk4_0)),esk6_0))
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_194,c_0_136])).

cnf(c_0_198,negated_conjecture,
    ( ~ l1_struct_0(esk6_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_196]),c_0_188]),c_0_103]),c_0_189])]),c_0_197])).

cnf(c_0_199,negated_conjecture,
    ( ~ l1_struct_0(esk6_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_42]),c_0_30]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_200,negated_conjecture,
    ( ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_109]),c_0_146])])).

cnf(c_0_201,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_109]),c_0_23])])).

cnf(c_0_202,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_30,c_0_201]),
    [proof]).

%------------------------------------------------------------------------------
