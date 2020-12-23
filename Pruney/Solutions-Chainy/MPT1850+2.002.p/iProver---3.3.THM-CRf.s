%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:30 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  209 (1885 expanded)
%              Number of clauses        :  117 ( 591 expanded)
%              Number of leaves         :   23 ( 439 expanded)
%              Depth                    :   23
%              Number of atoms          :  698 (7102 expanded)
%              Number of equality atoms :  264 (2024 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v1_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v1_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v1_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v1_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
     => ( ~ v1_tdlat_3(sK1)
        & v1_tdlat_3(X0)
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tdlat_3(X1)
            & v1_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ~ v1_tdlat_3(sK1)
    & v1_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f57,f56])).

fof(f88,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f70,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f83,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f69,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0) )
        & ( k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f84,plain,(
    ! [X0] :
      ( k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f63,f66])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f72,f66,f66,f66,f66])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f68,f66,f66])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f73,f66,f66,f66,f66])).

fof(f101,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f74,f66,f66])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f75,f66,f66])).

fof(f85,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1229,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2541,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
    | m1_pre_topc(sK0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1229])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1242,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1226,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3145,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1226])).

cnf(c_19,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_47,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_77,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7341,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3145,c_47,c_77])).

cnf(c_7342,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7341])).

cnf(c_7350,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2541,c_7342])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_31,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_49,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_7404,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7350])).

cnf(c_7814,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7350,c_31,c_49,c_7404])).

cnf(c_11,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1234,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7825,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7814,c_1234])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_32,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7969,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7825,c_32])).

cnf(c_18,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_10,plain,
    ( v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_165,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_10])).

cnf(c_166,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_1222,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166])).

cnf(c_1238,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1399,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1222,c_1238])).

cnf(c_8146,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK0,X0) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1399])).

cnf(c_8152,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK0,X0) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8146,c_28])).

cnf(c_27,negated_conjecture,
    ( v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,plain,
    ( v1_tdlat_3(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,plain,
    ( v1_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_41,plain,
    ( v1_tdlat_3(sK0) != iProver_top
    | v2_pre_topc(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_9,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1236,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2314,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1236])).

cnf(c_8217,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8152,c_31,c_33,c_41,c_2314])).

cnf(c_8218,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8217])).

cnf(c_8229,plain,
    ( m1_pre_topc(sK0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7969,c_8218])).

cnf(c_8706,plain,
    ( m1_pre_topc(sK0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8229,c_32])).

cnf(c_25,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_394,plain,
    ( ~ l1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_395,plain,
    ( ~ l1_pre_topc(sK0)
    | k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_36,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_397,plain,
    ( k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_30,c_27,c_36])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1241,plain,
    ( m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1260,plain,
    ( m1_subset_1(X0,k9_setfam_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1241,c_3])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
    | m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1233,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4302,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1233])).

cnf(c_7099,plain,
    ( m1_pre_topc(sK0,X0) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_397,c_4302])).

cnf(c_7599,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK0,X0) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7099,c_1233])).

cnf(c_12398,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) = iProver_top
    | m1_pre_topc(sK0,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7599,c_77])).

cnf(c_12399,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK0,X0) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_12398])).

cnf(c_12423,plain,
    ( m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8706,c_12399])).

cnf(c_12551,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12423,c_31,c_32,c_49])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1239,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12556,plain,
    ( r1_tarski(u1_pre_topc(sK0),k9_setfam_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12551,c_1239])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1243,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12971,plain,
    ( k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK0)
    | r1_tarski(k9_setfam_1(u1_struct_0(sK1)),u1_pre_topc(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12556,c_1243])).

cnf(c_8138,plain,
    ( m1_pre_topc(sK0,X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2541,c_1399])).

cnf(c_8212,plain,
    ( m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8138])).

cnf(c_7101,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4302,c_1239])).

cnf(c_7180,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(k9_setfam_1(u1_struct_0(X0)),u1_pre_topc(sK0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_397,c_7101])).

cnf(c_7418,plain,
    ( r1_tarski(k9_setfam_1(u1_struct_0(X0)),u1_pre_topc(sK0)) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7180,c_31])).

cnf(c_7419,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(k9_setfam_1(u1_struct_0(X0)),u1_pre_topc(sK0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7418])).

cnf(c_7427,plain,
    ( k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(sK0)
    | m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(u1_pre_topc(sK0),k9_setfam_1(u1_struct_0(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7419,c_1243])).

cnf(c_12972,plain,
    ( k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK0)
    | m1_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12556,c_7427])).

cnf(c_13095,plain,
    ( k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12971,c_31,c_32,c_33,c_41,c_49,c_2314,c_8212,c_12972])).

cnf(c_8,plain,
    ( m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1237,plain,
    ( m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2044,plain,
    ( r1_tarski(u1_pre_topc(X0),k9_setfam_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1239])).

cnf(c_13122,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_13095,c_2044])).

cnf(c_13,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1615,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4664,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),sK1)
    | ~ m1_pre_topc(sK1,X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1615])).

cnf(c_4665,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0) != iProver_top
    | v1_tops_2(u1_pre_topc(X0),sK1) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4664])).

cnf(c_4667,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0) != iProver_top
    | v1_tops_2(u1_pre_topc(sK0),sK1) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4665])).

cnf(c_1548,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(sK1))
    | ~ r1_tarski(u1_pre_topc(sK1),X0)
    | u1_pre_topc(sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3042,plain,
    ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0))
    | u1_pre_topc(sK1) = u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_3047,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(X0)
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) != iProver_top
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3042])).

cnf(c_3049,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK0)
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) != iProver_top
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3047])).

cnf(c_15,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
    | r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1997,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3041,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),sK1)
    | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1))))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_3043,plain,
    ( v1_tops_2(u1_pre_topc(X0),sK1) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3041])).

cnf(c_3045,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK1) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3043])).

cnf(c_643,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1472,plain,
    ( u1_pre_topc(sK1) != X0
    | k9_setfam_1(u1_struct_0(sK1)) != X0
    | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_1555,plain,
    ( u1_pre_topc(sK1) != u1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(sK1)) != u1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_1557,plain,
    ( u1_pre_topc(sK1) != u1_pre_topc(sK0)
    | k9_setfam_1(u1_struct_0(sK1)) != u1_pre_topc(sK0)
    | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_14,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1480,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1485,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0) = iProver_top
    | m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1480])).

cnf(c_1487,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0) = iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_1479,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1481,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1479])).

cnf(c_1483,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_24,plain,
    ( v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_26,negated_conjecture,
    ( ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_386,plain,
    ( ~ l1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_387,plain,
    ( ~ l1_pre_topc(sK1)
    | k9_setfam_1(u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_74,plain,
    ( m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_76,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13122,c_12972,c_12423,c_8212,c_4667,c_3049,c_3045,c_2314,c_1557,c_1487,c_1483,c_387,c_76,c_49,c_41,c_33,c_32,c_29,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.59/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/1.00  
% 3.59/1.00  ------  iProver source info
% 3.59/1.00  
% 3.59/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.59/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/1.00  git: non_committed_changes: false
% 3.59/1.00  git: last_make_outside_of_git: false
% 3.59/1.00  
% 3.59/1.00  ------ 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options
% 3.59/1.00  
% 3.59/1.00  --out_options                           all
% 3.59/1.00  --tptp_safe_out                         true
% 3.59/1.00  --problem_path                          ""
% 3.59/1.00  --include_path                          ""
% 3.59/1.00  --clausifier                            res/vclausify_rel
% 3.59/1.00  --clausifier_options                    --mode clausify
% 3.59/1.00  --stdin                                 false
% 3.59/1.00  --stats_out                             all
% 3.59/1.00  
% 3.59/1.00  ------ General Options
% 3.59/1.00  
% 3.59/1.00  --fof                                   false
% 3.59/1.00  --time_out_real                         305.
% 3.59/1.00  --time_out_virtual                      -1.
% 3.59/1.00  --symbol_type_check                     false
% 3.59/1.00  --clausify_out                          false
% 3.59/1.00  --sig_cnt_out                           false
% 3.59/1.00  --trig_cnt_out                          false
% 3.59/1.00  --trig_cnt_out_tolerance                1.
% 3.59/1.00  --trig_cnt_out_sk_spl                   false
% 3.59/1.00  --abstr_cl_out                          false
% 3.59/1.00  
% 3.59/1.00  ------ Global Options
% 3.59/1.00  
% 3.59/1.00  --schedule                              default
% 3.59/1.00  --add_important_lit                     false
% 3.59/1.00  --prop_solver_per_cl                    1000
% 3.59/1.00  --min_unsat_core                        false
% 3.59/1.00  --soft_assumptions                      false
% 3.59/1.00  --soft_lemma_size                       3
% 3.59/1.00  --prop_impl_unit_size                   0
% 3.59/1.00  --prop_impl_unit                        []
% 3.59/1.00  --share_sel_clauses                     true
% 3.59/1.00  --reset_solvers                         false
% 3.59/1.00  --bc_imp_inh                            [conj_cone]
% 3.59/1.00  --conj_cone_tolerance                   3.
% 3.59/1.00  --extra_neg_conj                        none
% 3.59/1.00  --large_theory_mode                     true
% 3.59/1.00  --prolific_symb_bound                   200
% 3.59/1.00  --lt_threshold                          2000
% 3.59/1.00  --clause_weak_htbl                      true
% 3.59/1.00  --gc_record_bc_elim                     false
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing Options
% 3.59/1.00  
% 3.59/1.00  --preprocessing_flag                    true
% 3.59/1.00  --time_out_prep_mult                    0.1
% 3.59/1.00  --splitting_mode                        input
% 3.59/1.00  --splitting_grd                         true
% 3.59/1.00  --splitting_cvd                         false
% 3.59/1.00  --splitting_cvd_svl                     false
% 3.59/1.00  --splitting_nvd                         32
% 3.59/1.00  --sub_typing                            true
% 3.59/1.00  --prep_gs_sim                           true
% 3.59/1.00  --prep_unflatten                        true
% 3.59/1.00  --prep_res_sim                          true
% 3.59/1.00  --prep_upred                            true
% 3.59/1.00  --prep_sem_filter                       exhaustive
% 3.59/1.00  --prep_sem_filter_out                   false
% 3.59/1.00  --pred_elim                             true
% 3.59/1.00  --res_sim_input                         true
% 3.59/1.00  --eq_ax_congr_red                       true
% 3.59/1.00  --pure_diseq_elim                       true
% 3.59/1.00  --brand_transform                       false
% 3.59/1.00  --non_eq_to_eq                          false
% 3.59/1.00  --prep_def_merge                        true
% 3.59/1.00  --prep_def_merge_prop_impl              false
% 3.59/1.00  --prep_def_merge_mbd                    true
% 3.59/1.00  --prep_def_merge_tr_red                 false
% 3.59/1.00  --prep_def_merge_tr_cl                  false
% 3.59/1.00  --smt_preprocessing                     true
% 3.59/1.00  --smt_ac_axioms                         fast
% 3.59/1.00  --preprocessed_out                      false
% 3.59/1.00  --preprocessed_stats                    false
% 3.59/1.00  
% 3.59/1.00  ------ Abstraction refinement Options
% 3.59/1.00  
% 3.59/1.00  --abstr_ref                             []
% 3.59/1.00  --abstr_ref_prep                        false
% 3.59/1.00  --abstr_ref_until_sat                   false
% 3.59/1.00  --abstr_ref_sig_restrict                funpre
% 3.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.00  --abstr_ref_under                       []
% 3.59/1.00  
% 3.59/1.00  ------ SAT Options
% 3.59/1.00  
% 3.59/1.00  --sat_mode                              false
% 3.59/1.00  --sat_fm_restart_options                ""
% 3.59/1.00  --sat_gr_def                            false
% 3.59/1.00  --sat_epr_types                         true
% 3.59/1.00  --sat_non_cyclic_types                  false
% 3.59/1.00  --sat_finite_models                     false
% 3.59/1.00  --sat_fm_lemmas                         false
% 3.59/1.00  --sat_fm_prep                           false
% 3.59/1.00  --sat_fm_uc_incr                        true
% 3.59/1.00  --sat_out_model                         small
% 3.59/1.00  --sat_out_clauses                       false
% 3.59/1.00  
% 3.59/1.00  ------ QBF Options
% 3.59/1.00  
% 3.59/1.00  --qbf_mode                              false
% 3.59/1.00  --qbf_elim_univ                         false
% 3.59/1.00  --qbf_dom_inst                          none
% 3.59/1.00  --qbf_dom_pre_inst                      false
% 3.59/1.00  --qbf_sk_in                             false
% 3.59/1.00  --qbf_pred_elim                         true
% 3.59/1.00  --qbf_split                             512
% 3.59/1.00  
% 3.59/1.00  ------ BMC1 Options
% 3.59/1.00  
% 3.59/1.00  --bmc1_incremental                      false
% 3.59/1.00  --bmc1_axioms                           reachable_all
% 3.59/1.00  --bmc1_min_bound                        0
% 3.59/1.00  --bmc1_max_bound                        -1
% 3.59/1.00  --bmc1_max_bound_default                -1
% 3.59/1.00  --bmc1_symbol_reachability              true
% 3.59/1.00  --bmc1_property_lemmas                  false
% 3.59/1.00  --bmc1_k_induction                      false
% 3.59/1.00  --bmc1_non_equiv_states                 false
% 3.59/1.00  --bmc1_deadlock                         false
% 3.59/1.00  --bmc1_ucm                              false
% 3.59/1.00  --bmc1_add_unsat_core                   none
% 3.59/1.00  --bmc1_unsat_core_children              false
% 3.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.00  --bmc1_out_stat                         full
% 3.59/1.00  --bmc1_ground_init                      false
% 3.59/1.00  --bmc1_pre_inst_next_state              false
% 3.59/1.00  --bmc1_pre_inst_state                   false
% 3.59/1.00  --bmc1_pre_inst_reach_state             false
% 3.59/1.00  --bmc1_out_unsat_core                   false
% 3.59/1.00  --bmc1_aig_witness_out                  false
% 3.59/1.00  --bmc1_verbose                          false
% 3.59/1.00  --bmc1_dump_clauses_tptp                false
% 3.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.00  --bmc1_dump_file                        -
% 3.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.00  --bmc1_ucm_extend_mode                  1
% 3.59/1.00  --bmc1_ucm_init_mode                    2
% 3.59/1.00  --bmc1_ucm_cone_mode                    none
% 3.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.00  --bmc1_ucm_relax_model                  4
% 3.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.00  --bmc1_ucm_layered_model                none
% 3.59/1.00  --bmc1_ucm_max_lemma_size               10
% 3.59/1.00  
% 3.59/1.00  ------ AIG Options
% 3.59/1.00  
% 3.59/1.00  --aig_mode                              false
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation Options
% 3.59/1.00  
% 3.59/1.00  --instantiation_flag                    true
% 3.59/1.00  --inst_sos_flag                         false
% 3.59/1.00  --inst_sos_phase                        true
% 3.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel_side                     num_symb
% 3.59/1.00  --inst_solver_per_active                1400
% 3.59/1.00  --inst_solver_calls_frac                1.
% 3.59/1.00  --inst_passive_queue_type               priority_queues
% 3.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.00  --inst_passive_queues_freq              [25;2]
% 3.59/1.00  --inst_dismatching                      true
% 3.59/1.00  --inst_eager_unprocessed_to_passive     true
% 3.59/1.00  --inst_prop_sim_given                   true
% 3.59/1.00  --inst_prop_sim_new                     false
% 3.59/1.00  --inst_subs_new                         false
% 3.59/1.00  --inst_eq_res_simp                      false
% 3.59/1.00  --inst_subs_given                       false
% 3.59/1.00  --inst_orphan_elimination               true
% 3.59/1.00  --inst_learning_loop_flag               true
% 3.59/1.00  --inst_learning_start                   3000
% 3.59/1.00  --inst_learning_factor                  2
% 3.59/1.00  --inst_start_prop_sim_after_learn       3
% 3.59/1.00  --inst_sel_renew                        solver
% 3.59/1.00  --inst_lit_activity_flag                true
% 3.59/1.00  --inst_restr_to_given                   false
% 3.59/1.00  --inst_activity_threshold               500
% 3.59/1.00  --inst_out_proof                        true
% 3.59/1.00  
% 3.59/1.00  ------ Resolution Options
% 3.59/1.00  
% 3.59/1.00  --resolution_flag                       true
% 3.59/1.00  --res_lit_sel                           adaptive
% 3.59/1.00  --res_lit_sel_side                      none
% 3.59/1.00  --res_ordering                          kbo
% 3.59/1.00  --res_to_prop_solver                    active
% 3.59/1.00  --res_prop_simpl_new                    false
% 3.59/1.00  --res_prop_simpl_given                  true
% 3.59/1.00  --res_passive_queue_type                priority_queues
% 3.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.00  --res_passive_queues_freq               [15;5]
% 3.59/1.00  --res_forward_subs                      full
% 3.59/1.00  --res_backward_subs                     full
% 3.59/1.00  --res_forward_subs_resolution           true
% 3.59/1.00  --res_backward_subs_resolution          true
% 3.59/1.00  --res_orphan_elimination                true
% 3.59/1.00  --res_time_limit                        2.
% 3.59/1.00  --res_out_proof                         true
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Options
% 3.59/1.00  
% 3.59/1.00  --superposition_flag                    true
% 3.59/1.00  --sup_passive_queue_type                priority_queues
% 3.59/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.59/1.00  --demod_completeness_check              fast
% 3.59/1.00  --demod_use_ground                      true
% 3.59/1.00  --sup_to_prop_solver                    passive
% 3.59/1.00  --sup_prop_simpl_new                    true
% 3.59/1.00  --sup_prop_simpl_given                  true
% 3.59/1.00  --sup_fun_splitting                     false
% 3.59/1.00  --sup_smt_interval                      50000
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Simplification Setup
% 3.59/1.00  
% 3.59/1.00  --sup_indices_passive                   []
% 3.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_full_bw                           [BwDemod]
% 3.59/1.00  --sup_immed_triv                        [TrivRules]
% 3.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_immed_bw_main                     []
% 3.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  
% 3.59/1.00  ------ Combination Options
% 3.59/1.00  
% 3.59/1.00  --comb_res_mult                         3
% 3.59/1.00  --comb_sup_mult                         2
% 3.59/1.00  --comb_inst_mult                        10
% 3.59/1.00  
% 3.59/1.00  ------ Debug Options
% 3.59/1.00  
% 3.59/1.00  --dbg_backtrace                         false
% 3.59/1.00  --dbg_dump_prop_clauses                 false
% 3.59/1.00  --dbg_dump_prop_clauses_file            -
% 3.59/1.00  --dbg_out_stat                          false
% 3.59/1.00  ------ Parsing...
% 3.59/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/1.00  ------ Proving...
% 3.59/1.00  ------ Problem Properties 
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  clauses                                 29
% 3.59/1.00  conjectures                             3
% 3.59/1.00  EPR                                     9
% 3.59/1.00  Horn                                    29
% 3.59/1.00  unary                                   10
% 3.59/1.00  binary                                  4
% 3.59/1.00  lits                                    80
% 3.59/1.00  lits eq                                 7
% 3.59/1.00  fd_pure                                 0
% 3.59/1.00  fd_pseudo                               0
% 3.59/1.00  fd_cond                                 0
% 3.59/1.00  fd_pseudo_cond                          1
% 3.59/1.00  AC symbols                              0
% 3.59/1.00  
% 3.59/1.00  ------ Schedule dynamic 5 is on 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  ------ 
% 3.59/1.00  Current options:
% 3.59/1.00  ------ 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options
% 3.59/1.00  
% 3.59/1.00  --out_options                           all
% 3.59/1.00  --tptp_safe_out                         true
% 3.59/1.00  --problem_path                          ""
% 3.59/1.00  --include_path                          ""
% 3.59/1.00  --clausifier                            res/vclausify_rel
% 3.59/1.00  --clausifier_options                    --mode clausify
% 3.59/1.00  --stdin                                 false
% 3.59/1.00  --stats_out                             all
% 3.59/1.00  
% 3.59/1.00  ------ General Options
% 3.59/1.00  
% 3.59/1.00  --fof                                   false
% 3.59/1.00  --time_out_real                         305.
% 3.59/1.00  --time_out_virtual                      -1.
% 3.59/1.00  --symbol_type_check                     false
% 3.59/1.00  --clausify_out                          false
% 3.59/1.00  --sig_cnt_out                           false
% 3.59/1.00  --trig_cnt_out                          false
% 3.59/1.00  --trig_cnt_out_tolerance                1.
% 3.59/1.00  --trig_cnt_out_sk_spl                   false
% 3.59/1.00  --abstr_cl_out                          false
% 3.59/1.00  
% 3.59/1.00  ------ Global Options
% 3.59/1.00  
% 3.59/1.00  --schedule                              default
% 3.59/1.00  --add_important_lit                     false
% 3.59/1.00  --prop_solver_per_cl                    1000
% 3.59/1.00  --min_unsat_core                        false
% 3.59/1.00  --soft_assumptions                      false
% 3.59/1.00  --soft_lemma_size                       3
% 3.59/1.00  --prop_impl_unit_size                   0
% 3.59/1.00  --prop_impl_unit                        []
% 3.59/1.00  --share_sel_clauses                     true
% 3.59/1.00  --reset_solvers                         false
% 3.59/1.00  --bc_imp_inh                            [conj_cone]
% 3.59/1.00  --conj_cone_tolerance                   3.
% 3.59/1.00  --extra_neg_conj                        none
% 3.59/1.00  --large_theory_mode                     true
% 3.59/1.00  --prolific_symb_bound                   200
% 3.59/1.00  --lt_threshold                          2000
% 3.59/1.00  --clause_weak_htbl                      true
% 3.59/1.00  --gc_record_bc_elim                     false
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing Options
% 3.59/1.00  
% 3.59/1.00  --preprocessing_flag                    true
% 3.59/1.00  --time_out_prep_mult                    0.1
% 3.59/1.00  --splitting_mode                        input
% 3.59/1.00  --splitting_grd                         true
% 3.59/1.00  --splitting_cvd                         false
% 3.59/1.00  --splitting_cvd_svl                     false
% 3.59/1.00  --splitting_nvd                         32
% 3.59/1.00  --sub_typing                            true
% 3.59/1.00  --prep_gs_sim                           true
% 3.59/1.00  --prep_unflatten                        true
% 3.59/1.00  --prep_res_sim                          true
% 3.59/1.00  --prep_upred                            true
% 3.59/1.00  --prep_sem_filter                       exhaustive
% 3.59/1.00  --prep_sem_filter_out                   false
% 3.59/1.00  --pred_elim                             true
% 3.59/1.00  --res_sim_input                         true
% 3.59/1.00  --eq_ax_congr_red                       true
% 3.59/1.00  --pure_diseq_elim                       true
% 3.59/1.00  --brand_transform                       false
% 3.59/1.00  --non_eq_to_eq                          false
% 3.59/1.00  --prep_def_merge                        true
% 3.59/1.00  --prep_def_merge_prop_impl              false
% 3.59/1.00  --prep_def_merge_mbd                    true
% 3.59/1.00  --prep_def_merge_tr_red                 false
% 3.59/1.00  --prep_def_merge_tr_cl                  false
% 3.59/1.00  --smt_preprocessing                     true
% 3.59/1.00  --smt_ac_axioms                         fast
% 3.59/1.00  --preprocessed_out                      false
% 3.59/1.00  --preprocessed_stats                    false
% 3.59/1.00  
% 3.59/1.00  ------ Abstraction refinement Options
% 3.59/1.00  
% 3.59/1.00  --abstr_ref                             []
% 3.59/1.00  --abstr_ref_prep                        false
% 3.59/1.00  --abstr_ref_until_sat                   false
% 3.59/1.00  --abstr_ref_sig_restrict                funpre
% 3.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.00  --abstr_ref_under                       []
% 3.59/1.00  
% 3.59/1.00  ------ SAT Options
% 3.59/1.00  
% 3.59/1.00  --sat_mode                              false
% 3.59/1.00  --sat_fm_restart_options                ""
% 3.59/1.00  --sat_gr_def                            false
% 3.59/1.00  --sat_epr_types                         true
% 3.59/1.00  --sat_non_cyclic_types                  false
% 3.59/1.00  --sat_finite_models                     false
% 3.59/1.00  --sat_fm_lemmas                         false
% 3.59/1.00  --sat_fm_prep                           false
% 3.59/1.00  --sat_fm_uc_incr                        true
% 3.59/1.00  --sat_out_model                         small
% 3.59/1.00  --sat_out_clauses                       false
% 3.59/1.00  
% 3.59/1.00  ------ QBF Options
% 3.59/1.00  
% 3.59/1.00  --qbf_mode                              false
% 3.59/1.00  --qbf_elim_univ                         false
% 3.59/1.00  --qbf_dom_inst                          none
% 3.59/1.00  --qbf_dom_pre_inst                      false
% 3.59/1.00  --qbf_sk_in                             false
% 3.59/1.00  --qbf_pred_elim                         true
% 3.59/1.00  --qbf_split                             512
% 3.59/1.00  
% 3.59/1.00  ------ BMC1 Options
% 3.59/1.00  
% 3.59/1.00  --bmc1_incremental                      false
% 3.59/1.00  --bmc1_axioms                           reachable_all
% 3.59/1.00  --bmc1_min_bound                        0
% 3.59/1.00  --bmc1_max_bound                        -1
% 3.59/1.00  --bmc1_max_bound_default                -1
% 3.59/1.00  --bmc1_symbol_reachability              true
% 3.59/1.00  --bmc1_property_lemmas                  false
% 3.59/1.00  --bmc1_k_induction                      false
% 3.59/1.00  --bmc1_non_equiv_states                 false
% 3.59/1.00  --bmc1_deadlock                         false
% 3.59/1.00  --bmc1_ucm                              false
% 3.59/1.00  --bmc1_add_unsat_core                   none
% 3.59/1.00  --bmc1_unsat_core_children              false
% 3.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.00  --bmc1_out_stat                         full
% 3.59/1.00  --bmc1_ground_init                      false
% 3.59/1.00  --bmc1_pre_inst_next_state              false
% 3.59/1.00  --bmc1_pre_inst_state                   false
% 3.59/1.00  --bmc1_pre_inst_reach_state             false
% 3.59/1.00  --bmc1_out_unsat_core                   false
% 3.59/1.00  --bmc1_aig_witness_out                  false
% 3.59/1.00  --bmc1_verbose                          false
% 3.59/1.00  --bmc1_dump_clauses_tptp                false
% 3.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.00  --bmc1_dump_file                        -
% 3.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.00  --bmc1_ucm_extend_mode                  1
% 3.59/1.00  --bmc1_ucm_init_mode                    2
% 3.59/1.00  --bmc1_ucm_cone_mode                    none
% 3.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.00  --bmc1_ucm_relax_model                  4
% 3.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.00  --bmc1_ucm_layered_model                none
% 3.59/1.00  --bmc1_ucm_max_lemma_size               10
% 3.59/1.00  
% 3.59/1.00  ------ AIG Options
% 3.59/1.00  
% 3.59/1.00  --aig_mode                              false
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation Options
% 3.59/1.00  
% 3.59/1.00  --instantiation_flag                    true
% 3.59/1.00  --inst_sos_flag                         false
% 3.59/1.00  --inst_sos_phase                        true
% 3.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel_side                     none
% 3.59/1.00  --inst_solver_per_active                1400
% 3.59/1.00  --inst_solver_calls_frac                1.
% 3.59/1.00  --inst_passive_queue_type               priority_queues
% 3.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.00  --inst_passive_queues_freq              [25;2]
% 3.59/1.00  --inst_dismatching                      true
% 3.59/1.00  --inst_eager_unprocessed_to_passive     true
% 3.59/1.00  --inst_prop_sim_given                   true
% 3.59/1.00  --inst_prop_sim_new                     false
% 3.59/1.00  --inst_subs_new                         false
% 3.59/1.00  --inst_eq_res_simp                      false
% 3.59/1.00  --inst_subs_given                       false
% 3.59/1.00  --inst_orphan_elimination               true
% 3.59/1.00  --inst_learning_loop_flag               true
% 3.59/1.00  --inst_learning_start                   3000
% 3.59/1.00  --inst_learning_factor                  2
% 3.59/1.00  --inst_start_prop_sim_after_learn       3
% 3.59/1.00  --inst_sel_renew                        solver
% 3.59/1.00  --inst_lit_activity_flag                true
% 3.59/1.00  --inst_restr_to_given                   false
% 3.59/1.00  --inst_activity_threshold               500
% 3.59/1.00  --inst_out_proof                        true
% 3.59/1.00  
% 3.59/1.00  ------ Resolution Options
% 3.59/1.00  
% 3.59/1.00  --resolution_flag                       false
% 3.59/1.00  --res_lit_sel                           adaptive
% 3.59/1.00  --res_lit_sel_side                      none
% 3.59/1.00  --res_ordering                          kbo
% 3.59/1.00  --res_to_prop_solver                    active
% 3.59/1.00  --res_prop_simpl_new                    false
% 3.59/1.00  --res_prop_simpl_given                  true
% 3.59/1.00  --res_passive_queue_type                priority_queues
% 3.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.00  --res_passive_queues_freq               [15;5]
% 3.59/1.00  --res_forward_subs                      full
% 3.59/1.00  --res_backward_subs                     full
% 3.59/1.00  --res_forward_subs_resolution           true
% 3.59/1.00  --res_backward_subs_resolution          true
% 3.59/1.00  --res_orphan_elimination                true
% 3.59/1.00  --res_time_limit                        2.
% 3.59/1.00  --res_out_proof                         true
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Options
% 3.59/1.00  
% 3.59/1.00  --superposition_flag                    true
% 3.59/1.00  --sup_passive_queue_type                priority_queues
% 3.59/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.59/1.00  --demod_completeness_check              fast
% 3.59/1.00  --demod_use_ground                      true
% 3.59/1.00  --sup_to_prop_solver                    passive
% 3.59/1.00  --sup_prop_simpl_new                    true
% 3.59/1.00  --sup_prop_simpl_given                  true
% 3.59/1.00  --sup_fun_splitting                     false
% 3.59/1.00  --sup_smt_interval                      50000
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Simplification Setup
% 3.59/1.00  
% 3.59/1.00  --sup_indices_passive                   []
% 3.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_full_bw                           [BwDemod]
% 3.59/1.00  --sup_immed_triv                        [TrivRules]
% 3.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_immed_bw_main                     []
% 3.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  
% 3.59/1.00  ------ Combination Options
% 3.59/1.00  
% 3.59/1.00  --comb_res_mult                         3
% 3.59/1.00  --comb_sup_mult                         2
% 3.59/1.00  --comb_inst_mult                        10
% 3.59/1.00  
% 3.59/1.00  ------ Debug Options
% 3.59/1.00  
% 3.59/1.00  --dbg_backtrace                         false
% 3.59/1.00  --dbg_dump_prop_clauses                 false
% 3.59/1.00  --dbg_dump_prop_clauses_file            -
% 3.59/1.00  --dbg_out_stat                          false
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  ------ Proving...
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  % SZS status Theorem for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  fof(f21,conjecture,(
% 3.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f22,negated_conjecture,(
% 3.59/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 3.59/1.00    inference(negated_conjecture,[],[f21])).
% 3.59/1.00  
% 3.59/1.00  fof(f47,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : ((~v1_tdlat_3(X1) & (v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f22])).
% 3.59/1.00  
% 3.59/1.00  fof(f48,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.59/1.00    inference(flattening,[],[f47])).
% 3.59/1.00  
% 3.59/1.00  fof(f57,plain,(
% 3.59/1.00    ( ! [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) => (~v1_tdlat_3(sK1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(sK1))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f56,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f58,plain,(
% 3.59/1.00    (~v1_tdlat_3(sK1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f57,f56])).
% 3.59/1.00  
% 3.59/1.00  fof(f88,plain,(
% 3.59/1.00    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 3.59/1.00    inference(cnf_transformation,[],[f58])).
% 3.59/1.00  
% 3.59/1.00  fof(f14,axiom,(
% 3.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f23,plain,(
% 3.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 3.59/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.59/1.00  
% 3.59/1.00  fof(f36,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f23])).
% 3.59/1.00  
% 3.59/1.00  fof(f76,plain,(
% 3.59/1.00    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f36])).
% 3.59/1.00  
% 3.59/1.00  fof(f1,axiom,(
% 3.59/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f49,plain,(
% 3.59/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/1.00    inference(nnf_transformation,[],[f1])).
% 3.59/1.00  
% 3.59/1.00  fof(f50,plain,(
% 3.59/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/1.00    inference(flattening,[],[f49])).
% 3.59/1.00  
% 3.59/1.00  fof(f59,plain,(
% 3.59/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.59/1.00    inference(cnf_transformation,[],[f50])).
% 3.59/1.00  
% 3.59/1.00  fof(f100,plain,(
% 3.59/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/1.00    inference(equality_resolution,[],[f59])).
% 3.59/1.00  
% 3.59/1.00  fof(f17,axiom,(
% 3.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f40,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f17])).
% 3.59/1.00  
% 3.59/1.00  fof(f41,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.59/1.00    inference(flattening,[],[f40])).
% 3.59/1.00  
% 3.59/1.00  fof(f54,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.59/1.00    inference(nnf_transformation,[],[f41])).
% 3.59/1.00  
% 3.59/1.00  fof(f80,plain,(
% 3.59/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f54])).
% 3.59/1.00  
% 3.59/1.00  fof(f16,axiom,(
% 3.59/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f39,plain,(
% 3.59/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f16])).
% 3.59/1.00  
% 3.59/1.00  fof(f79,plain,(
% 3.59/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f39])).
% 3.59/1.00  
% 3.59/1.00  fof(f6,axiom,(
% 3.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f25,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f6])).
% 3.59/1.00  
% 3.59/1.00  fof(f67,plain,(
% 3.59/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f25])).
% 3.59/1.00  
% 3.59/1.00  fof(f86,plain,(
% 3.59/1.00    l1_pre_topc(sK0)),
% 3.59/1.00    inference(cnf_transformation,[],[f58])).
% 3.59/1.00  
% 3.59/1.00  fof(f10,axiom,(
% 3.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f31,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f10])).
% 3.59/1.00  
% 3.59/1.00  fof(f71,plain,(
% 3.59/1.00    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f31])).
% 3.59/1.00  
% 3.59/1.00  fof(f87,plain,(
% 3.59/1.00    l1_pre_topc(sK1)),
% 3.59/1.00    inference(cnf_transformation,[],[f58])).
% 3.59/1.00  
% 3.59/1.00  fof(f15,axiom,(
% 3.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f37,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f15])).
% 3.59/1.00  
% 3.59/1.00  fof(f38,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(flattening,[],[f37])).
% 3.59/1.00  
% 3.59/1.00  fof(f53,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(nnf_transformation,[],[f38])).
% 3.59/1.00  
% 3.59/1.00  fof(f77,plain,(
% 3.59/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f53])).
% 3.59/1.00  
% 3.59/1.00  fof(f103,plain,(
% 3.59/1.00    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 3.59/1.00    inference(equality_resolution,[],[f77])).
% 3.59/1.00  
% 3.59/1.00  fof(f9,axiom,(
% 3.59/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => v2_pre_topc(X0)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f29,plain,(
% 3.59/1.00    ! [X0] : ((v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f9])).
% 3.59/1.00  
% 3.59/1.00  fof(f30,plain,(
% 3.59/1.00    ! [X0] : (v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(flattening,[],[f29])).
% 3.59/1.00  
% 3.59/1.00  fof(f70,plain,(
% 3.59/1.00    ( ! [X0] : (v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f30])).
% 3.59/1.00  
% 3.59/1.00  fof(f89,plain,(
% 3.59/1.00    v1_tdlat_3(sK0)),
% 3.59/1.00    inference(cnf_transformation,[],[f58])).
% 3.59/1.00  
% 3.59/1.00  fof(f19,axiom,(
% 3.59/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f44,plain,(
% 3.59/1.00    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f19])).
% 3.59/1.00  
% 3.59/1.00  fof(f45,plain,(
% 3.59/1.00    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(flattening,[],[f44])).
% 3.59/1.00  
% 3.59/1.00  fof(f83,plain,(
% 3.59/1.00    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f45])).
% 3.59/1.00  
% 3.59/1.00  fof(f8,axiom,(
% 3.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f24,plain,(
% 3.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.59/1.00    inference(pure_predicate_removal,[],[f8])).
% 3.59/1.00  
% 3.59/1.00  fof(f27,plain,(
% 3.59/1.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f24])).
% 3.59/1.00  
% 3.59/1.00  fof(f28,plain,(
% 3.59/1.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.59/1.00    inference(flattening,[],[f27])).
% 3.59/1.00  
% 3.59/1.00  fof(f69,plain,(
% 3.59/1.00    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f28])).
% 3.59/1.00  
% 3.59/1.00  fof(f20,axiom,(
% 3.59/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) <=> k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f46,plain,(
% 3.59/1.00    ! [X0] : ((v1_tdlat_3(X0) <=> k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f20])).
% 3.59/1.00  
% 3.59/1.00  fof(f55,plain,(
% 3.59/1.00    ! [X0] : (((v1_tdlat_3(X0) | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0)) & (k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 3.59/1.01    inference(nnf_transformation,[],[f46])).
% 3.59/1.01  
% 3.59/1.01  fof(f84,plain,(
% 3.59/1.01    ( ! [X0] : (k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f55])).
% 3.59/1.01  
% 3.59/1.01  fof(f3,axiom,(
% 3.59/1.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f63,plain,(
% 3.59/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.59/1.01    inference(cnf_transformation,[],[f3])).
% 3.59/1.01  
% 3.59/1.01  fof(f5,axiom,(
% 3.59/1.01    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f66,plain,(
% 3.59/1.01    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f5])).
% 3.59/1.01  
% 3.59/1.01  fof(f91,plain,(
% 3.59/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0))) )),
% 3.59/1.01    inference(definition_unfolding,[],[f63,f66])).
% 3.59/1.01  
% 3.59/1.01  fof(f2,axiom,(
% 3.59/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f62,plain,(
% 3.59/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.59/1.01    inference(cnf_transformation,[],[f2])).
% 3.59/1.01  
% 3.59/1.01  fof(f11,axiom,(
% 3.59/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f32,plain,(
% 3.59/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.59/1.01    inference(ennf_transformation,[],[f11])).
% 3.59/1.01  
% 3.59/1.01  fof(f72,plain,(
% 3.59/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f32])).
% 3.59/1.01  
% 3.59/1.01  fof(f95,plain,(
% 3.59/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f72,f66,f66,f66,f66])).
% 3.59/1.01  
% 3.59/1.01  fof(f4,axiom,(
% 3.59/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f51,plain,(
% 3.59/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.59/1.01    inference(nnf_transformation,[],[f4])).
% 3.59/1.01  
% 3.59/1.01  fof(f64,plain,(
% 3.59/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.59/1.01    inference(cnf_transformation,[],[f51])).
% 3.59/1.01  
% 3.59/1.01  fof(f93,plain,(
% 3.59/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k9_setfam_1(X1))) )),
% 3.59/1.01    inference(definition_unfolding,[],[f64,f66])).
% 3.59/1.01  
% 3.59/1.01  fof(f61,plain,(
% 3.59/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f50])).
% 3.59/1.01  
% 3.59/1.01  fof(f7,axiom,(
% 3.59/1.01    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f26,plain,(
% 3.59/1.01    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.59/1.01    inference(ennf_transformation,[],[f7])).
% 3.59/1.01  
% 3.59/1.01  fof(f68,plain,(
% 3.59/1.01    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f26])).
% 3.59/1.01  
% 3.59/1.01  fof(f94,plain,(
% 3.59/1.01    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f68,f66,f66])).
% 3.59/1.01  
% 3.59/1.01  fof(f12,axiom,(
% 3.59/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f33,plain,(
% 3.59/1.01    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.59/1.01    inference(ennf_transformation,[],[f12])).
% 3.59/1.01  
% 3.59/1.01  fof(f34,plain,(
% 3.59/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.59/1.01    inference(flattening,[],[f33])).
% 3.59/1.01  
% 3.59/1.01  fof(f73,plain,(
% 3.59/1.01    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f34])).
% 3.59/1.01  
% 3.59/1.01  fof(f96,plain,(
% 3.59/1.01    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f73,f66,f66,f66,f66])).
% 3.59/1.01  
% 3.59/1.01  fof(f101,plain,(
% 3.59/1.01    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(equality_resolution,[],[f96])).
% 3.59/1.01  
% 3.59/1.01  fof(f13,axiom,(
% 3.59/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f35,plain,(
% 3.59/1.01    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.59/1.01    inference(ennf_transformation,[],[f13])).
% 3.59/1.01  
% 3.59/1.01  fof(f52,plain,(
% 3.59/1.01    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.59/1.01    inference(nnf_transformation,[],[f35])).
% 3.59/1.01  
% 3.59/1.01  fof(f74,plain,(
% 3.59/1.01    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f52])).
% 3.59/1.01  
% 3.59/1.01  fof(f98,plain,(
% 3.59/1.01    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f74,f66,f66])).
% 3.59/1.01  
% 3.59/1.01  fof(f75,plain,(
% 3.59/1.01    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f52])).
% 3.59/1.01  
% 3.59/1.01  fof(f97,plain,(
% 3.59/1.01    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f75,f66,f66])).
% 3.59/1.01  
% 3.59/1.01  fof(f85,plain,(
% 3.59/1.01    ( ! [X0] : (v1_tdlat_3(X0) | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f55])).
% 3.59/1.01  
% 3.59/1.01  fof(f90,plain,(
% 3.59/1.01    ~v1_tdlat_3(sK1)),
% 3.59/1.01    inference(cnf_transformation,[],[f58])).
% 3.59/1.01  
% 3.59/1.01  cnf(c_28,negated_conjecture,
% 3.59/1.01      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 3.59/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_16,plain,
% 3.59/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.59/1.01      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.59/1.01      | ~ l1_pre_topc(X1) ),
% 3.59/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1229,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2541,plain,
% 3.59/1.01      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
% 3.59/1.01      | m1_pre_topc(sK0,X0) != iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_28,c_1229]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2,plain,
% 3.59/1.01      ( r1_tarski(X0,X0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1242,plain,
% 3.59/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_21,plain,
% 3.59/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.59/1.01      | ~ m1_pre_topc(X2,X1)
% 3.59/1.01      | m1_pre_topc(X0,X2)
% 3.59/1.01      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.59/1.01      | ~ v2_pre_topc(X1)
% 3.59/1.01      | ~ l1_pre_topc(X1) ),
% 3.59/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1226,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | m1_pre_topc(X2,X1) != iProver_top
% 3.59/1.01      | m1_pre_topc(X0,X2) = iProver_top
% 3.59/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 3.59/1.01      | v2_pre_topc(X1) != iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3145,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | m1_pre_topc(X0,X0) = iProver_top
% 3.59/1.01      | v2_pre_topc(X1) != iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_1242,c_1226]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_19,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_47,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X0) = iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7,plain,
% 3.59/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_77,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top
% 3.59/1.01      | l1_pre_topc(X0) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7341,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X0) = iProver_top
% 3.59/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_3145,c_47,c_77]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7342,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | m1_pre_topc(X0,X0) = iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(renaming,[status(thm)],[c_7341]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7350,plain,
% 3.59/1.01      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.59/1.01      | m1_pre_topc(sK0,X0) != iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_2541,c_7342]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_30,negated_conjecture,
% 3.59/1.01      ( l1_pre_topc(sK0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_31,plain,
% 3.59/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_49,plain,
% 3.59/1.01      ( m1_pre_topc(sK0,sK0) = iProver_top
% 3.59/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_47]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7404,plain,
% 3.59/1.01      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.59/1.01      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.59/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_7350]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7814,plain,
% 3.59/1.01      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_7350,c_31,c_49,c_7404]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_11,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1)
% 3.59/1.01      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.59/1.01      | ~ l1_pre_topc(X1) ),
% 3.59/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1234,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) = iProver_top
% 3.59/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7825,plain,
% 3.59/1.01      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top
% 3.59/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_7814,c_1234]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_29,negated_conjecture,
% 3.59/1.01      ( l1_pre_topc(sK1) ),
% 3.59/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_32,plain,
% 3.59/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7969,plain,
% 3.59/1.01      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_7825,c_32]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_18,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1)
% 3.59/1.01      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.59/1.01      | ~ v2_pre_topc(X0)
% 3.59/1.01      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.59/1.01      | ~ l1_pre_topc(X1)
% 3.59/1.01      | ~ l1_pre_topc(X0)
% 3.59/1.01      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.59/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_10,plain,
% 3.59/1.01      ( v2_pre_topc(X0)
% 3.59/1.01      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.59/1.01      | ~ l1_pre_topc(X0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_165,plain,
% 3.59/1.01      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.59/1.01      | m1_pre_topc(X0,X1)
% 3.59/1.01      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.59/1.01      | ~ l1_pre_topc(X1)
% 3.59/1.01      | ~ l1_pre_topc(X0)
% 3.59/1.01      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_18,c_10]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_166,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1)
% 3.59/1.01      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.59/1.01      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.59/1.01      | ~ l1_pre_topc(X0)
% 3.59/1.01      | ~ l1_pre_topc(X1)
% 3.59/1.01      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.59/1.01      inference(renaming,[status(thm)],[c_165]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1222,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) = iProver_top
% 3.59/1.01      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 3.59/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top
% 3.59/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_166]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1238,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top
% 3.59/1.01      | l1_pre_topc(X0) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1399,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) = iProver_top
% 3.59/1.01      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 3.59/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(forward_subsumption_resolution,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_1222,c_1238]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_8146,plain,
% 3.59/1.01      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 3.59/1.01      | m1_pre_topc(sK0,X0) = iProver_top
% 3.59/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top
% 3.59/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_28,c_1399]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_8152,plain,
% 3.59/1.01      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 3.59/1.01      | m1_pre_topc(sK0,X0) = iProver_top
% 3.59/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top
% 3.59/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.59/1.01      inference(light_normalisation,[status(thm)],[c_8146,c_28]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_27,negated_conjecture,
% 3.59/1.01      ( v1_tdlat_3(sK0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_33,plain,
% 3.59/1.01      ( v1_tdlat_3(sK0) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_23,plain,
% 3.59/1.01      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_39,plain,
% 3.59/1.01      ( v1_tdlat_3(X0) != iProver_top
% 3.59/1.01      | v2_pre_topc(X0) = iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_41,plain,
% 3.59/1.01      ( v1_tdlat_3(sK0) != iProver_top
% 3.59/1.01      | v2_pre_topc(sK0) = iProver_top
% 3.59/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_39]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_9,plain,
% 3.59/1.01      ( ~ v2_pre_topc(X0)
% 3.59/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.59/1.01      | ~ l1_pre_topc(X0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1236,plain,
% 3.59/1.01      ( v2_pre_topc(X0) != iProver_top
% 3.59/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2314,plain,
% 3.59/1.01      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.59/1.01      | v2_pre_topc(sK0) != iProver_top
% 3.59/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_28,c_1236]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_8217,plain,
% 3.59/1.01      ( l1_pre_topc(X0) != iProver_top
% 3.59/1.01      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 3.59/1.01      | m1_pre_topc(sK0,X0) = iProver_top ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_8152,c_31,c_33,c_41,c_2314]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_8218,plain,
% 3.59/1.01      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 3.59/1.01      | m1_pre_topc(sK0,X0) = iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(renaming,[status(thm)],[c_8217]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_8229,plain,
% 3.59/1.01      ( m1_pre_topc(sK0,sK1) = iProver_top
% 3.59/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_7969,c_8218]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_8706,plain,
% 3.59/1.01      ( m1_pre_topc(sK0,sK1) = iProver_top ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_8229,c_32]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_25,plain,
% 3.59/1.01      ( ~ v1_tdlat_3(X0)
% 3.59/1.01      | ~ l1_pre_topc(X0)
% 3.59/1.01      | k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_394,plain,
% 3.59/1.01      ( ~ l1_pre_topc(X0)
% 3.59/1.01      | k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)
% 3.59/1.01      | sK0 != X0 ),
% 3.59/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_395,plain,
% 3.59/1.01      ( ~ l1_pre_topc(sK0)
% 3.59/1.01      | k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
% 3.59/1.01      inference(unflattening,[status(thm)],[c_394]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_36,plain,
% 3.59/1.01      ( ~ v1_tdlat_3(sK0)
% 3.59/1.01      | ~ l1_pre_topc(sK0)
% 3.59/1.01      | k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_25]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_397,plain,
% 3.59/1.01      ( k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_395,c_30,c_27,c_36]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_4,plain,
% 3.59/1.01      ( m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0)) ),
% 3.59/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1241,plain,
% 3.59/1.01      ( m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0)) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3,plain,
% 3.59/1.01      ( k2_subset_1(X0) = X0 ),
% 3.59/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1260,plain,
% 3.59/1.01      ( m1_subset_1(X0,k9_setfam_1(X0)) = iProver_top ),
% 3.59/1.01      inference(light_normalisation,[status(thm)],[c_1241,c_3]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_12,plain,
% 3.59/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.59/1.01      | ~ m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
% 3.59/1.01      | m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
% 3.59/1.01      | ~ l1_pre_topc(X1) ),
% 3.59/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1233,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) != iProver_top
% 3.59/1.01      | m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) = iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_4302,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | m1_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) = iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_1260,c_1233]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7099,plain,
% 3.59/1.01      ( m1_pre_topc(sK0,X0) != iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) = iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_397,c_4302]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7599,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | m1_pre_topc(sK0,X0) != iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) = iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_7099,c_1233]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_12398,plain,
% 3.59/1.01      ( m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) = iProver_top
% 3.59/1.01      | m1_pre_topc(sK0,X0) != iProver_top
% 3.59/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_7599,c_77]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_12399,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | m1_pre_topc(sK0,X0) != iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) = iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(renaming,[status(thm)],[c_12398]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_12423,plain,
% 3.59/1.01      ( m1_pre_topc(sK0,sK0) != iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) = iProver_top
% 3.59/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_8706,c_12399]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_12551,plain,
% 3.59/1.01      ( m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_12423,c_31,c_32,c_49]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_6,plain,
% 3.59/1.01      ( ~ m1_subset_1(X0,k9_setfam_1(X1)) | r1_tarski(X0,X1) ),
% 3.59/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1239,plain,
% 3.59/1.01      ( m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top
% 3.59/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_12556,plain,
% 3.59/1.01      ( r1_tarski(u1_pre_topc(sK0),k9_setfam_1(u1_struct_0(sK1))) = iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_12551,c_1239]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_0,plain,
% 3.59/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.59/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1243,plain,
% 3.59/1.01      ( X0 = X1
% 3.59/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.59/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_12971,plain,
% 3.59/1.01      ( k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK0)
% 3.59/1.01      | r1_tarski(k9_setfam_1(u1_struct_0(sK1)),u1_pre_topc(sK0)) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_12556,c_1243]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_8138,plain,
% 3.59/1.01      ( m1_pre_topc(sK0,X0) != iProver_top
% 3.59/1.01      | m1_pre_topc(sK1,X0) = iProver_top
% 3.59/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top
% 3.59/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_2541,c_1399]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_8212,plain,
% 3.59/1.01      ( m1_pre_topc(sK0,sK0) != iProver_top
% 3.59/1.01      | m1_pre_topc(sK1,sK0) = iProver_top
% 3.59/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.59/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.59/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_8138]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7101,plain,
% 3.59/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.59/1.01      | r1_tarski(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X1))) = iProver_top
% 3.59/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_4302,c_1239]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7180,plain,
% 3.59/1.01      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.59/1.01      | r1_tarski(k9_setfam_1(u1_struct_0(X0)),u1_pre_topc(sK0)) = iProver_top
% 3.59/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_397,c_7101]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7418,plain,
% 3.59/1.01      ( r1_tarski(k9_setfam_1(u1_struct_0(X0)),u1_pre_topc(sK0)) = iProver_top
% 3.59/1.01      | m1_pre_topc(X0,sK0) != iProver_top ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_7180,c_31]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7419,plain,
% 3.59/1.01      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.59/1.01      | r1_tarski(k9_setfam_1(u1_struct_0(X0)),u1_pre_topc(sK0)) = iProver_top ),
% 3.59/1.01      inference(renaming,[status(thm)],[c_7418]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7427,plain,
% 3.59/1.01      ( k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(sK0)
% 3.59/1.01      | m1_pre_topc(X0,sK0) != iProver_top
% 3.59/1.01      | r1_tarski(u1_pre_topc(sK0),k9_setfam_1(u1_struct_0(X0))) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_7419,c_1243]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_12972,plain,
% 3.59/1.01      ( k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK0)
% 3.59/1.01      | m1_pre_topc(sK1,sK0) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_12556,c_7427]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_13095,plain,
% 3.59/1.01      ( k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK0) ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_12971,c_31,c_32,c_33,c_41,c_49,c_2314,c_8212,c_12972]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_8,plain,
% 3.59/1.01      ( m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
% 3.59/1.01      | ~ l1_pre_topc(X0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1237,plain,
% 3.59/1.01      ( m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) = iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2044,plain,
% 3.59/1.01      ( r1_tarski(u1_pre_topc(X0),k9_setfam_1(u1_struct_0(X0))) = iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_1237,c_1239]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_13122,plain,
% 3.59/1.01      ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) = iProver_top
% 3.59/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_13095,c_2044]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_13,plain,
% 3.59/1.01      ( ~ v1_tops_2(X0,X1)
% 3.59/1.01      | v1_tops_2(X0,X2)
% 3.59/1.01      | ~ m1_pre_topc(X2,X1)
% 3.59/1.01      | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(u1_struct_0(X2))))
% 3.59/1.01      | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
% 3.59/1.01      | ~ l1_pre_topc(X1) ),
% 3.59/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1615,plain,
% 3.59/1.01      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 3.59/1.01      | v1_tops_2(u1_pre_topc(X0),X1)
% 3.59/1.01      | ~ m1_pre_topc(X1,X0)
% 3.59/1.01      | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
% 3.59/1.01      | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
% 3.59/1.01      | ~ l1_pre_topc(X0) ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_4664,plain,
% 3.59/1.01      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 3.59/1.01      | v1_tops_2(u1_pre_topc(X0),sK1)
% 3.59/1.01      | ~ m1_pre_topc(sK1,X0)
% 3.59/1.01      | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
% 3.59/1.01      | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1))))
% 3.59/1.01      | ~ l1_pre_topc(X0) ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_1615]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_4665,plain,
% 3.59/1.01      ( v1_tops_2(u1_pre_topc(X0),X0) != iProver_top
% 3.59/1.01      | v1_tops_2(u1_pre_topc(X0),sK1) = iProver_top
% 3.59/1.01      | m1_pre_topc(sK1,X0) != iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) != iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) != iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_4664]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_4667,plain,
% 3.59/1.01      ( v1_tops_2(u1_pre_topc(sK0),sK0) != iProver_top
% 3.59/1.01      | v1_tops_2(u1_pre_topc(sK0),sK1) = iProver_top
% 3.59/1.01      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) != iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) != iProver_top
% 3.59/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_4665]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1548,plain,
% 3.59/1.01      ( ~ r1_tarski(X0,u1_pre_topc(sK1))
% 3.59/1.01      | ~ r1_tarski(u1_pre_topc(sK1),X0)
% 3.59/1.01      | u1_pre_topc(sK1) = X0 ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3042,plain,
% 3.59/1.01      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
% 3.59/1.01      | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0))
% 3.59/1.01      | u1_pre_topc(sK1) = u1_pre_topc(X0) ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_1548]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3047,plain,
% 3.59/1.01      ( u1_pre_topc(sK1) = u1_pre_topc(X0)
% 3.59/1.01      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) != iProver_top
% 3.59/1.01      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0)) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_3042]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3049,plain,
% 3.59/1.01      ( u1_pre_topc(sK1) = u1_pre_topc(sK0)
% 3.59/1.01      | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) != iProver_top
% 3.59/1.01      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) != iProver_top ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_3047]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_15,plain,
% 3.59/1.01      ( ~ v1_tops_2(X0,X1)
% 3.59/1.01      | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
% 3.59/1.01      | r1_tarski(X0,u1_pre_topc(X1))
% 3.59/1.01      | ~ l1_pre_topc(X1) ),
% 3.59/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1997,plain,
% 3.59/1.01      ( ~ v1_tops_2(u1_pre_topc(X0),X1)
% 3.59/1.01      | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
% 3.59/1.01      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
% 3.59/1.01      | ~ l1_pre_topc(X1) ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3041,plain,
% 3.59/1.01      ( ~ v1_tops_2(u1_pre_topc(X0),sK1)
% 3.59/1.01      | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1))))
% 3.59/1.01      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
% 3.59/1.01      | ~ l1_pre_topc(sK1) ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_1997]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3043,plain,
% 3.59/1.01      ( v1_tops_2(u1_pre_topc(X0),sK1) != iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) != iProver_top
% 3.59/1.01      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) = iProver_top
% 3.59/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_3041]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3045,plain,
% 3.59/1.01      ( v1_tops_2(u1_pre_topc(sK0),sK1) != iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) != iProver_top
% 3.59/1.01      | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) = iProver_top
% 3.59/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_3043]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_643,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1472,plain,
% 3.59/1.01      ( u1_pre_topc(sK1) != X0
% 3.59/1.01      | k9_setfam_1(u1_struct_0(sK1)) != X0
% 3.59/1.01      | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1) ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_643]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1555,plain,
% 3.59/1.01      ( u1_pre_topc(sK1) != u1_pre_topc(X0)
% 3.59/1.01      | k9_setfam_1(u1_struct_0(sK1)) != u1_pre_topc(X0)
% 3.59/1.01      | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1) ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_1472]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1557,plain,
% 3.59/1.01      ( u1_pre_topc(sK1) != u1_pre_topc(sK0)
% 3.59/1.01      | k9_setfam_1(u1_struct_0(sK1)) != u1_pre_topc(sK0)
% 3.59/1.01      | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1) ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_1555]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_14,plain,
% 3.59/1.01      ( v1_tops_2(X0,X1)
% 3.59/1.01      | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
% 3.59/1.01      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 3.59/1.01      | ~ l1_pre_topc(X1) ),
% 3.59/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1480,plain,
% 3.59/1.01      ( v1_tops_2(u1_pre_topc(X0),X0)
% 3.59/1.01      | ~ m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
% 3.59/1.01      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
% 3.59/1.01      | ~ l1_pre_topc(X0) ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1485,plain,
% 3.59/1.01      ( v1_tops_2(u1_pre_topc(X0),X0) = iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) != iProver_top
% 3.59/1.01      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) != iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_1480]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1487,plain,
% 3.59/1.01      ( v1_tops_2(u1_pre_topc(sK0),sK0) = iProver_top
% 3.59/1.01      | m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) != iProver_top
% 3.59/1.01      | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) != iProver_top
% 3.59/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_1485]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1479,plain,
% 3.59/1.01      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1481,plain,
% 3.59/1.01      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_1479]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1483,plain,
% 3.59/1.01      ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) = iProver_top ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_1481]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_24,plain,
% 3.59/1.01      ( v1_tdlat_3(X0)
% 3.59/1.01      | ~ l1_pre_topc(X0)
% 3.59/1.01      | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_26,negated_conjecture,
% 3.59/1.01      ( ~ v1_tdlat_3(sK1) ),
% 3.59/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_386,plain,
% 3.59/1.01      ( ~ l1_pre_topc(X0)
% 3.59/1.01      | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0)
% 3.59/1.01      | sK1 != X0 ),
% 3.59/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_26]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_387,plain,
% 3.59/1.01      ( ~ l1_pre_topc(sK1)
% 3.59/1.01      | k9_setfam_1(u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
% 3.59/1.01      inference(unflattening,[status(thm)],[c_386]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_74,plain,
% 3.59/1.01      ( m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) = iProver_top
% 3.59/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_76,plain,
% 3.59/1.01      ( m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) = iProver_top
% 3.59/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_74]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(contradiction,plain,
% 3.59/1.01      ( $false ),
% 3.59/1.01      inference(minisat,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_13122,c_12972,c_12423,c_8212,c_4667,c_3049,c_3045,
% 3.59/1.01                 c_2314,c_1557,c_1487,c_1483,c_387,c_76,c_49,c_41,c_33,
% 3.59/1.01                 c_32,c_29,c_31]) ).
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/1.01  
% 3.59/1.01  ------                               Statistics
% 3.59/1.01  
% 3.59/1.01  ------ General
% 3.59/1.01  
% 3.59/1.01  abstr_ref_over_cycles:                  0
% 3.59/1.01  abstr_ref_under_cycles:                 0
% 3.59/1.01  gc_basic_clause_elim:                   0
% 3.59/1.01  forced_gc_time:                         0
% 3.59/1.01  parsing_time:                           0.01
% 3.59/1.01  unif_index_cands_time:                  0.
% 3.59/1.01  unif_index_add_time:                    0.
% 3.59/1.01  orderings_time:                         0.
% 3.59/1.01  out_proof_time:                         0.016
% 3.59/1.01  total_time:                             0.341
% 3.59/1.01  num_of_symbols:                         45
% 3.59/1.01  num_of_terms:                           5918
% 3.59/1.01  
% 3.59/1.01  ------ Preprocessing
% 3.59/1.01  
% 3.59/1.01  num_of_splits:                          0
% 3.59/1.01  num_of_split_atoms:                     0
% 3.59/1.01  num_of_reused_defs:                     0
% 3.59/1.01  num_eq_ax_congr_red:                    9
% 3.59/1.01  num_of_sem_filtered_clauses:            1
% 3.59/1.01  num_of_subtypes:                        0
% 3.59/1.01  monotx_restored_types:                  0
% 3.59/1.01  sat_num_of_epr_types:                   0
% 3.59/1.01  sat_num_of_non_cyclic_types:            0
% 3.59/1.01  sat_guarded_non_collapsed_types:        0
% 3.59/1.01  num_pure_diseq_elim:                    0
% 3.59/1.01  simp_replaced_by:                       0
% 3.59/1.01  res_preprocessed:                       139
% 3.59/1.01  prep_upred:                             0
% 3.59/1.01  prep_unflattend:                        3
% 3.59/1.01  smt_new_axioms:                         0
% 3.59/1.01  pred_elim_cands:                        6
% 3.59/1.01  pred_elim:                              1
% 3.59/1.01  pred_elim_cl:                           0
% 3.59/1.01  pred_elim_cycles:                       3
% 3.59/1.01  merged_defs:                            8
% 3.59/1.01  merged_defs_ncl:                        0
% 3.59/1.01  bin_hyper_res:                          8
% 3.59/1.01  prep_cycles:                            4
% 3.59/1.01  pred_elim_time:                         0.002
% 3.59/1.01  splitting_time:                         0.
% 3.59/1.01  sem_filter_time:                        0.
% 3.59/1.01  monotx_time:                            0.001
% 3.59/1.01  subtype_inf_time:                       0.
% 3.59/1.01  
% 3.59/1.01  ------ Problem properties
% 3.59/1.01  
% 3.59/1.01  clauses:                                29
% 3.59/1.01  conjectures:                            3
% 3.59/1.01  epr:                                    9
% 3.59/1.01  horn:                                   29
% 3.59/1.01  ground:                                 7
% 3.59/1.01  unary:                                  10
% 3.59/1.01  binary:                                 4
% 3.59/1.01  lits:                                   80
% 3.59/1.01  lits_eq:                                7
% 3.59/1.01  fd_pure:                                0
% 3.59/1.01  fd_pseudo:                              0
% 3.59/1.01  fd_cond:                                0
% 3.59/1.01  fd_pseudo_cond:                         1
% 3.59/1.01  ac_symbols:                             0
% 3.59/1.01  
% 3.59/1.01  ------ Propositional Solver
% 3.59/1.01  
% 3.59/1.01  prop_solver_calls:                      29
% 3.59/1.01  prop_fast_solver_calls:                 1283
% 3.59/1.01  smt_solver_calls:                       0
% 3.59/1.01  smt_fast_solver_calls:                  0
% 3.59/1.01  prop_num_of_clauses:                    3909
% 3.59/1.01  prop_preprocess_simplified:             10709
% 3.59/1.01  prop_fo_subsumed:                       83
% 3.59/1.01  prop_solver_time:                       0.
% 3.59/1.01  smt_solver_time:                        0.
% 3.59/1.01  smt_fast_solver_time:                   0.
% 3.59/1.01  prop_fast_solver_time:                  0.
% 3.59/1.01  prop_unsat_core_time:                   0.
% 3.59/1.01  
% 3.59/1.01  ------ QBF
% 3.59/1.01  
% 3.59/1.01  qbf_q_res:                              0
% 3.59/1.01  qbf_num_tautologies:                    0
% 3.59/1.01  qbf_prep_cycles:                        0
% 3.59/1.01  
% 3.59/1.01  ------ BMC1
% 3.59/1.01  
% 3.59/1.01  bmc1_current_bound:                     -1
% 3.59/1.01  bmc1_last_solved_bound:                 -1
% 3.59/1.01  bmc1_unsat_core_size:                   -1
% 3.59/1.01  bmc1_unsat_core_parents_size:           -1
% 3.59/1.01  bmc1_merge_next_fun:                    0
% 3.59/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.59/1.01  
% 3.59/1.01  ------ Instantiation
% 3.59/1.01  
% 3.59/1.01  inst_num_of_clauses:                    1295
% 3.59/1.01  inst_num_in_passive:                    139
% 3.59/1.01  inst_num_in_active:                     569
% 3.59/1.01  inst_num_in_unprocessed:                588
% 3.59/1.01  inst_num_of_loops:                      590
% 3.59/1.01  inst_num_of_learning_restarts:          0
% 3.59/1.01  inst_num_moves_active_passive:          18
% 3.59/1.01  inst_lit_activity:                      0
% 3.59/1.01  inst_lit_activity_moves:                0
% 3.59/1.01  inst_num_tautologies:                   0
% 3.59/1.01  inst_num_prop_implied:                  0
% 3.59/1.01  inst_num_existing_simplified:           0
% 3.59/1.01  inst_num_eq_res_simplified:             0
% 3.59/1.01  inst_num_child_elim:                    0
% 3.59/1.01  inst_num_of_dismatching_blockings:      1026
% 3.59/1.01  inst_num_of_non_proper_insts:           1995
% 3.59/1.01  inst_num_of_duplicates:                 0
% 3.59/1.01  inst_inst_num_from_inst_to_res:         0
% 3.59/1.01  inst_dismatching_checking_time:         0.
% 3.59/1.01  
% 3.59/1.01  ------ Resolution
% 3.59/1.01  
% 3.59/1.01  res_num_of_clauses:                     0
% 3.59/1.01  res_num_in_passive:                     0
% 3.59/1.01  res_num_in_active:                      0
% 3.59/1.01  res_num_of_loops:                       143
% 3.59/1.01  res_forward_subset_subsumed:            230
% 3.59/1.01  res_backward_subset_subsumed:           6
% 3.59/1.01  res_forward_subsumed:                   0
% 3.59/1.01  res_backward_subsumed:                  0
% 3.59/1.01  res_forward_subsumption_resolution:     0
% 3.59/1.01  res_backward_subsumption_resolution:    0
% 3.59/1.01  res_clause_to_clause_subsumption:       1975
% 3.59/1.01  res_orphan_elimination:                 0
% 3.59/1.01  res_tautology_del:                      136
% 3.59/1.01  res_num_eq_res_simplified:              0
% 3.59/1.01  res_num_sel_changes:                    0
% 3.59/1.01  res_moves_from_active_to_pass:          0
% 3.59/1.01  
% 3.59/1.01  ------ Superposition
% 3.59/1.01  
% 3.59/1.01  sup_time_total:                         0.
% 3.59/1.01  sup_time_generating:                    0.
% 3.59/1.01  sup_time_sim_full:                      0.
% 3.59/1.01  sup_time_sim_immed:                     0.
% 3.59/1.01  
% 3.59/1.01  sup_num_of_clauses:                     257
% 3.59/1.01  sup_num_in_active:                      114
% 3.59/1.01  sup_num_in_passive:                     143
% 3.59/1.01  sup_num_of_loops:                       116
% 3.59/1.01  sup_fw_superposition:                   258
% 3.59/1.01  sup_bw_superposition:                   254
% 3.59/1.01  sup_immediate_simplified:               176
% 3.59/1.01  sup_given_eliminated:                   0
% 3.59/1.01  comparisons_done:                       0
% 3.59/1.01  comparisons_avoided:                    0
% 3.59/1.01  
% 3.59/1.01  ------ Simplifications
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  sim_fw_subset_subsumed:                 81
% 3.59/1.01  sim_bw_subset_subsumed:                 15
% 3.59/1.01  sim_fw_subsumed:                        70
% 3.59/1.01  sim_bw_subsumed:                        5
% 3.59/1.01  sim_fw_subsumption_res:                 6
% 3.59/1.01  sim_bw_subsumption_res:                 1
% 3.59/1.01  sim_tautology_del:                      32
% 3.59/1.01  sim_eq_tautology_del:                   2
% 3.59/1.01  sim_eq_res_simp:                        0
% 3.59/1.01  sim_fw_demodulated:                     1
% 3.59/1.01  sim_bw_demodulated:                     3
% 3.59/1.01  sim_light_normalised:                   29
% 3.59/1.01  sim_joinable_taut:                      0
% 3.59/1.01  sim_joinable_simp:                      0
% 3.59/1.01  sim_ac_normalised:                      0
% 3.59/1.01  sim_smt_subsumption:                    0
% 3.59/1.01  
%------------------------------------------------------------------------------
