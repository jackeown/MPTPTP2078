%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:30 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :  219 (1413 expanded)
%              Number of clauses        :  149 ( 529 expanded)
%              Number of leaves         :   21 ( 309 expanded)
%              Depth                    :   25
%              Number of atoms          :  710 (5511 expanded)
%              Number of equality atoms :  354 (1500 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v1_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v1_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v1_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v1_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f46,plain,
    ( ~ v1_tdlat_3(sK1)
    & v1_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f45,f44])).

fof(f69,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f12,axiom,(
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f21,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_808,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_136,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_3])).

cnf(c_137,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_136])).

cnf(c_803,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137])).

cnf(c_1435,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_803])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1504,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1435,c_25])).

cnf(c_1505,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1504])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_813,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1625,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1505,c_813])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1884,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1625,c_26])).

cnf(c_1885,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1884])).

cnf(c_1892,plain,
    ( m1_pre_topc(sK0,sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_1885])).

cnf(c_40,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_42,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_1649,plain,
    ( m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_2080,plain,
    ( m1_pre_topc(sK0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1892,c_25,c_26,c_42,c_1649])).

cnf(c_4,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_816,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_812,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2440,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_816,c_812])).

cnf(c_65,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3494,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2440,c_65])).

cnf(c_3495,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3494])).

cnf(c_3501,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3495,c_812])).

cnf(c_817,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4613,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3501,c_817])).

cnf(c_4620,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2080,c_4613])).

cnf(c_6679,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4620,c_26])).

cnf(c_6680,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6679])).

cnf(c_13,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_809,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6689,plain,
    ( v1_tops_2(u1_pre_topc(X0),sK1) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6680,c_809])).

cnf(c_7081,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v1_tops_2(u1_pre_topc(X0),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6689,c_26])).

cnf(c_7082,plain,
    ( v1_tops_2(u1_pre_topc(X0),sK1) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7081])).

cnf(c_3503,plain,
    ( v1_tops_2(u1_pre_topc(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3495,c_809])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_819,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3662,plain,
    ( u1_pre_topc(X0) = u1_pre_topc(X1)
    | v1_tops_2(u1_pre_topc(X1),X0) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3503,c_819])).

cnf(c_7092,plain,
    ( u1_pre_topc(X0) = u1_pre_topc(sK1)
    | v1_tops_2(u1_pre_topc(X0),sK1) != iProver_top
    | v1_tops_2(u1_pre_topc(sK1),X0) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7082,c_3662])).

cnf(c_7118,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | v1_tops_2(u1_pre_topc(sK0),sK1) != iProver_top
    | v1_tops_2(u1_pre_topc(sK1),sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7092])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_818,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_810,plain,
    ( v1_tops_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6688,plain,
    ( v1_tops_2(u1_pre_topc(X0),sK1) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6680,c_810])).

cnf(c_6960,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v1_tops_2(u1_pre_topc(X0),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6688,c_26])).

cnf(c_6961,plain,
    ( v1_tops_2(u1_pre_topc(X0),sK1) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6960])).

cnf(c_6969,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_6961])).

cnf(c_1009,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1127,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_1130,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_1527,plain,
    ( v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2159,plain,
    ( v1_tops_2(u1_pre_topc(X0),sK1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1527])).

cnf(c_3223,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2159])).

cnf(c_3224,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1) = iProver_top
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3223])).

cnf(c_3347,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3352,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3347])).

cnf(c_6977,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6969,c_26,c_1130,c_3224,c_3352])).

cnf(c_1626,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_813])).

cnf(c_1653,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1626,c_25])).

cnf(c_1654,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1653])).

cnf(c_1662,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_1654])).

cnf(c_4621,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_4613])).

cnf(c_1661,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_1654])).

cnf(c_1895,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1661,c_26])).

cnf(c_1896,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1895])).

cnf(c_1903,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_1896])).

cnf(c_2218,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1903,c_26])).

cnf(c_4622,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2218,c_4613])).

cnf(c_5477,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4621,c_25,c_26,c_1625,c_1626,c_4622])).

cnf(c_5487,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1505,c_5477])).

cnf(c_11,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_811,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | v1_tops_2(X0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_940,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | v1_tops_2(X0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_811,c_812])).

cnf(c_6114,plain,
    ( v1_tops_2(u1_pre_topc(X0),X1) != iProver_top
    | v1_tops_2(u1_pre_topc(X0),sK0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5487,c_940])).

cnf(c_6982,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK0) = iProver_top
    | m1_pre_topc(sK0,sK1) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6977,c_6114])).

cnf(c_453,plain,
    ( X0 != X1
    | k9_setfam_1(X0) = k9_setfam_1(X1) ),
    theory(equality)).

cnf(c_1772,plain,
    ( X0 != u1_struct_0(sK0)
    | k9_setfam_1(X0) = k9_setfam_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_3123,plain,
    ( k9_setfam_1(u1_struct_0(X0)) = k9_setfam_1(u1_struct_0(sK0))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1772])).

cnf(c_6416,plain,
    ( k9_setfam_1(u1_struct_0(sK1)) = k9_setfam_1(u1_struct_0(sK0))
    | u1_struct_0(sK1) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3123])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_807,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2329,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2218,c_807])).

cnf(c_21,negated_conjecture,
    ( v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27,plain,
    ( v1_tdlat_3(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_33,plain,
    ( v1_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_35,plain,
    ( v1_tdlat_3(sK0) != iProver_top
    | v2_pre_topc(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_4079,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2329,c_25,c_27,c_35])).

cnf(c_2327,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK0,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2080,c_807])).

cnf(c_5,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_815,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1351,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_815])).

cnf(c_1361,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1351,c_25,c_27,c_35])).

cnf(c_6,plain,
    ( v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_814,plain,
    ( v2_pre_topc(X0) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1366,plain,
    ( v2_pre_topc(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_814])).

cnf(c_3956,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK0,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2327,c_26,c_1366])).

cnf(c_3965,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK0)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK0,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3956,c_819])).

cnf(c_4449,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK0,sK1) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4079,c_3965])).

cnf(c_1005,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3318,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_3319,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3318])).

cnf(c_3321,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | m1_pre_topc(sK0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3319])).

cnf(c_2224,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2218,c_1885])).

cnf(c_1065,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1906,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),sK1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1065])).

cnf(c_1907,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0) != iProver_top
    | v1_tops_2(u1_pre_topc(X0),sK1) = iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1906])).

cnf(c_1909,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0) != iProver_top
    | v1_tops_2(u1_pre_topc(sK0),sK1) = iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1907])).

cnf(c_443,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1001,plain,
    ( k9_setfam_1(u1_struct_0(sK1)) != X0
    | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_1694,plain,
    ( k9_setfam_1(u1_struct_0(sK1)) != k9_setfam_1(u1_struct_0(sK0))
    | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_1079,plain,
    ( X0 != X1
    | u1_pre_topc(X2) != X1
    | u1_pre_topc(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_1248,plain,
    ( X0 != u1_pre_topc(X1)
    | u1_pre_topc(X2) = X0
    | u1_pre_topc(X2) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_1474,plain,
    ( k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
    | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(sK0))
    | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_1693,plain,
    ( k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
    | u1_pre_topc(sK1) = k9_setfam_1(u1_struct_0(sK0))
    | u1_pre_topc(sK1) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1474])).

cnf(c_1042,plain,
    ( X0 != X1
    | u1_pre_topc(sK1) != X1
    | u1_pre_topc(sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_1163,plain,
    ( X0 != u1_pre_topc(sK1)
    | u1_pre_topc(sK1) = X0
    | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_1232,plain,
    ( u1_pre_topc(X0) != u1_pre_topc(sK1)
    | u1_pre_topc(sK1) = u1_pre_topc(X0)
    | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_1234,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | u1_pre_topc(sK1) = u1_pre_topc(sK0)
    | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_442,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1121,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_447,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_1044,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(X0)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_1120,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_1014,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(c_1016,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_1008,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1010,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0) = iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_1012,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0) = iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_18,plain,
    ( v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_20,negated_conjecture,
    ( ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_272,plain,
    ( ~ l1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_273,plain,
    ( ~ l1_pre_topc(sK1)
    | k9_setfam_1(u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_62,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_64,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_19,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7118,c_6982,c_6416,c_4449,c_3321,c_2224,c_1909,c_1903,c_1694,c_1693,c_1649,c_1234,c_1121,c_1120,c_1016,c_1012,c_273,c_64,c_42,c_30,c_21,c_26,c_23,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:06:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.96/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/0.92  
% 2.96/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.96/0.92  
% 2.96/0.92  ------  iProver source info
% 2.96/0.92  
% 2.96/0.92  git: date: 2020-06-30 10:37:57 +0100
% 2.96/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.96/0.92  git: non_committed_changes: false
% 2.96/0.92  git: last_make_outside_of_git: false
% 2.96/0.92  
% 2.96/0.92  ------ 
% 2.96/0.92  
% 2.96/0.92  ------ Input Options
% 2.96/0.92  
% 2.96/0.92  --out_options                           all
% 2.96/0.92  --tptp_safe_out                         true
% 2.96/0.92  --problem_path                          ""
% 2.96/0.92  --include_path                          ""
% 2.96/0.92  --clausifier                            res/vclausify_rel
% 2.96/0.92  --clausifier_options                    --mode clausify
% 2.96/0.92  --stdin                                 false
% 2.96/0.92  --stats_out                             all
% 2.96/0.92  
% 2.96/0.92  ------ General Options
% 2.96/0.92  
% 2.96/0.92  --fof                                   false
% 2.96/0.92  --time_out_real                         305.
% 2.96/0.92  --time_out_virtual                      -1.
% 2.96/0.92  --symbol_type_check                     false
% 2.96/0.92  --clausify_out                          false
% 2.96/0.92  --sig_cnt_out                           false
% 2.96/0.92  --trig_cnt_out                          false
% 2.96/0.92  --trig_cnt_out_tolerance                1.
% 2.96/0.92  --trig_cnt_out_sk_spl                   false
% 2.96/0.92  --abstr_cl_out                          false
% 2.96/0.92  
% 2.96/0.92  ------ Global Options
% 2.96/0.92  
% 2.96/0.92  --schedule                              default
% 2.96/0.92  --add_important_lit                     false
% 2.96/0.92  --prop_solver_per_cl                    1000
% 2.96/0.92  --min_unsat_core                        false
% 2.96/0.92  --soft_assumptions                      false
% 2.96/0.92  --soft_lemma_size                       3
% 2.96/0.92  --prop_impl_unit_size                   0
% 2.96/0.92  --prop_impl_unit                        []
% 2.96/0.92  --share_sel_clauses                     true
% 2.96/0.92  --reset_solvers                         false
% 2.96/0.92  --bc_imp_inh                            [conj_cone]
% 2.96/0.92  --conj_cone_tolerance                   3.
% 2.96/0.92  --extra_neg_conj                        none
% 2.96/0.92  --large_theory_mode                     true
% 2.96/0.92  --prolific_symb_bound                   200
% 2.96/0.92  --lt_threshold                          2000
% 2.96/0.92  --clause_weak_htbl                      true
% 2.96/0.92  --gc_record_bc_elim                     false
% 2.96/0.92  
% 2.96/0.92  ------ Preprocessing Options
% 2.96/0.92  
% 2.96/0.92  --preprocessing_flag                    true
% 2.96/0.92  --time_out_prep_mult                    0.1
% 2.96/0.92  --splitting_mode                        input
% 2.96/0.92  --splitting_grd                         true
% 2.96/0.92  --splitting_cvd                         false
% 2.96/0.92  --splitting_cvd_svl                     false
% 2.96/0.92  --splitting_nvd                         32
% 2.96/0.92  --sub_typing                            true
% 2.96/0.92  --prep_gs_sim                           true
% 2.96/0.92  --prep_unflatten                        true
% 2.96/0.92  --prep_res_sim                          true
% 2.96/0.92  --prep_upred                            true
% 2.96/0.92  --prep_sem_filter                       exhaustive
% 2.96/0.92  --prep_sem_filter_out                   false
% 2.96/0.92  --pred_elim                             true
% 2.96/0.92  --res_sim_input                         true
% 2.96/0.92  --eq_ax_congr_red                       true
% 2.96/0.92  --pure_diseq_elim                       true
% 2.96/0.92  --brand_transform                       false
% 2.96/0.92  --non_eq_to_eq                          false
% 2.96/0.92  --prep_def_merge                        true
% 2.96/0.92  --prep_def_merge_prop_impl              false
% 2.96/0.92  --prep_def_merge_mbd                    true
% 2.96/0.92  --prep_def_merge_tr_red                 false
% 2.96/0.92  --prep_def_merge_tr_cl                  false
% 2.96/0.92  --smt_preprocessing                     true
% 2.96/0.92  --smt_ac_axioms                         fast
% 2.96/0.92  --preprocessed_out                      false
% 2.96/0.92  --preprocessed_stats                    false
% 2.96/0.92  
% 2.96/0.92  ------ Abstraction refinement Options
% 2.96/0.92  
% 2.96/0.92  --abstr_ref                             []
% 2.96/0.92  --abstr_ref_prep                        false
% 2.96/0.92  --abstr_ref_until_sat                   false
% 2.96/0.92  --abstr_ref_sig_restrict                funpre
% 2.96/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/0.92  --abstr_ref_under                       []
% 2.96/0.92  
% 2.96/0.92  ------ SAT Options
% 2.96/0.92  
% 2.96/0.92  --sat_mode                              false
% 2.96/0.92  --sat_fm_restart_options                ""
% 2.96/0.92  --sat_gr_def                            false
% 2.96/0.92  --sat_epr_types                         true
% 2.96/0.92  --sat_non_cyclic_types                  false
% 2.96/0.92  --sat_finite_models                     false
% 2.96/0.92  --sat_fm_lemmas                         false
% 2.96/0.92  --sat_fm_prep                           false
% 2.96/0.92  --sat_fm_uc_incr                        true
% 2.96/0.92  --sat_out_model                         small
% 2.96/0.92  --sat_out_clauses                       false
% 2.96/0.92  
% 2.96/0.92  ------ QBF Options
% 2.96/0.92  
% 2.96/0.92  --qbf_mode                              false
% 2.96/0.92  --qbf_elim_univ                         false
% 2.96/0.92  --qbf_dom_inst                          none
% 2.96/0.92  --qbf_dom_pre_inst                      false
% 2.96/0.92  --qbf_sk_in                             false
% 2.96/0.92  --qbf_pred_elim                         true
% 2.96/0.92  --qbf_split                             512
% 2.96/0.92  
% 2.96/0.92  ------ BMC1 Options
% 2.96/0.92  
% 2.96/0.92  --bmc1_incremental                      false
% 2.96/0.92  --bmc1_axioms                           reachable_all
% 2.96/0.92  --bmc1_min_bound                        0
% 2.96/0.92  --bmc1_max_bound                        -1
% 2.96/0.92  --bmc1_max_bound_default                -1
% 2.96/0.92  --bmc1_symbol_reachability              true
% 2.96/0.92  --bmc1_property_lemmas                  false
% 2.96/0.92  --bmc1_k_induction                      false
% 2.96/0.92  --bmc1_non_equiv_states                 false
% 2.96/0.92  --bmc1_deadlock                         false
% 2.96/0.92  --bmc1_ucm                              false
% 2.96/0.92  --bmc1_add_unsat_core                   none
% 2.96/0.92  --bmc1_unsat_core_children              false
% 2.96/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/0.92  --bmc1_out_stat                         full
% 2.96/0.92  --bmc1_ground_init                      false
% 2.96/0.92  --bmc1_pre_inst_next_state              false
% 2.96/0.92  --bmc1_pre_inst_state                   false
% 2.96/0.92  --bmc1_pre_inst_reach_state             false
% 2.96/0.92  --bmc1_out_unsat_core                   false
% 2.96/0.92  --bmc1_aig_witness_out                  false
% 2.96/0.92  --bmc1_verbose                          false
% 2.96/0.92  --bmc1_dump_clauses_tptp                false
% 2.96/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.96/0.92  --bmc1_dump_file                        -
% 2.96/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.96/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.96/0.92  --bmc1_ucm_extend_mode                  1
% 2.96/0.92  --bmc1_ucm_init_mode                    2
% 2.96/0.92  --bmc1_ucm_cone_mode                    none
% 2.96/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.96/0.92  --bmc1_ucm_relax_model                  4
% 2.96/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.96/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/0.92  --bmc1_ucm_layered_model                none
% 2.96/0.92  --bmc1_ucm_max_lemma_size               10
% 2.96/0.92  
% 2.96/0.92  ------ AIG Options
% 2.96/0.92  
% 2.96/0.92  --aig_mode                              false
% 2.96/0.92  
% 2.96/0.92  ------ Instantiation Options
% 2.96/0.92  
% 2.96/0.92  --instantiation_flag                    true
% 2.96/0.92  --inst_sos_flag                         false
% 2.96/0.92  --inst_sos_phase                        true
% 2.96/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/0.92  --inst_lit_sel_side                     num_symb
% 2.96/0.92  --inst_solver_per_active                1400
% 2.96/0.92  --inst_solver_calls_frac                1.
% 2.96/0.92  --inst_passive_queue_type               priority_queues
% 2.96/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/0.92  --inst_passive_queues_freq              [25;2]
% 2.96/0.92  --inst_dismatching                      true
% 2.96/0.92  --inst_eager_unprocessed_to_passive     true
% 2.96/0.92  --inst_prop_sim_given                   true
% 2.96/0.92  --inst_prop_sim_new                     false
% 2.96/0.92  --inst_subs_new                         false
% 2.96/0.92  --inst_eq_res_simp                      false
% 2.96/0.92  --inst_subs_given                       false
% 2.96/0.92  --inst_orphan_elimination               true
% 2.96/0.92  --inst_learning_loop_flag               true
% 2.96/0.92  --inst_learning_start                   3000
% 2.96/0.92  --inst_learning_factor                  2
% 2.96/0.92  --inst_start_prop_sim_after_learn       3
% 2.96/0.92  --inst_sel_renew                        solver
% 2.96/0.92  --inst_lit_activity_flag                true
% 2.96/0.92  --inst_restr_to_given                   false
% 2.96/0.92  --inst_activity_threshold               500
% 2.96/0.92  --inst_out_proof                        true
% 2.96/0.92  
% 2.96/0.92  ------ Resolution Options
% 2.96/0.92  
% 2.96/0.92  --resolution_flag                       true
% 2.96/0.92  --res_lit_sel                           adaptive
% 2.96/0.92  --res_lit_sel_side                      none
% 2.96/0.92  --res_ordering                          kbo
% 2.96/0.92  --res_to_prop_solver                    active
% 2.96/0.92  --res_prop_simpl_new                    false
% 2.96/0.92  --res_prop_simpl_given                  true
% 2.96/0.92  --res_passive_queue_type                priority_queues
% 2.96/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/0.92  --res_passive_queues_freq               [15;5]
% 2.96/0.92  --res_forward_subs                      full
% 2.96/0.92  --res_backward_subs                     full
% 2.96/0.92  --res_forward_subs_resolution           true
% 2.96/0.92  --res_backward_subs_resolution          true
% 2.96/0.92  --res_orphan_elimination                true
% 2.96/0.92  --res_time_limit                        2.
% 2.96/0.92  --res_out_proof                         true
% 2.96/0.92  
% 2.96/0.92  ------ Superposition Options
% 2.96/0.92  
% 2.96/0.92  --superposition_flag                    true
% 2.96/0.92  --sup_passive_queue_type                priority_queues
% 2.96/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.96/0.92  --demod_completeness_check              fast
% 2.96/0.92  --demod_use_ground                      true
% 2.96/0.92  --sup_to_prop_solver                    passive
% 2.96/0.92  --sup_prop_simpl_new                    true
% 2.96/0.92  --sup_prop_simpl_given                  true
% 2.96/0.92  --sup_fun_splitting                     false
% 2.96/0.92  --sup_smt_interval                      50000
% 2.96/0.92  
% 2.96/0.92  ------ Superposition Simplification Setup
% 2.96/0.92  
% 2.96/0.92  --sup_indices_passive                   []
% 2.96/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.92  --sup_full_bw                           [BwDemod]
% 2.96/0.92  --sup_immed_triv                        [TrivRules]
% 2.96/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.92  --sup_immed_bw_main                     []
% 2.96/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.92  
% 2.96/0.92  ------ Combination Options
% 2.96/0.92  
% 2.96/0.92  --comb_res_mult                         3
% 2.96/0.92  --comb_sup_mult                         2
% 2.96/0.92  --comb_inst_mult                        10
% 2.96/0.92  
% 2.96/0.92  ------ Debug Options
% 2.96/0.92  
% 2.96/0.92  --dbg_backtrace                         false
% 2.96/0.92  --dbg_dump_prop_clauses                 false
% 2.96/0.92  --dbg_dump_prop_clauses_file            -
% 2.96/0.92  --dbg_out_stat                          false
% 2.96/0.92  ------ Parsing...
% 2.96/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.96/0.92  
% 2.96/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.96/0.92  
% 2.96/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.96/0.92  
% 2.96/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.96/0.92  ------ Proving...
% 2.96/0.92  ------ Problem Properties 
% 2.96/0.92  
% 2.96/0.92  
% 2.96/0.92  clauses                                 23
% 2.96/0.92  conjectures                             3
% 2.96/0.92  EPR                                     8
% 2.96/0.92  Horn                                    23
% 2.96/0.92  unary                                   8
% 2.96/0.92  binary                                  2
% 2.96/0.92  lits                                    63
% 2.96/0.92  lits eq                                 6
% 2.96/0.92  fd_pure                                 0
% 2.96/0.92  fd_pseudo                               0
% 2.96/0.92  fd_cond                                 0
% 2.96/0.92  fd_pseudo_cond                          1
% 2.96/0.92  AC symbols                              0
% 2.96/0.92  
% 2.96/0.92  ------ Schedule dynamic 5 is on 
% 2.96/0.92  
% 2.96/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.96/0.92  
% 2.96/0.92  
% 2.96/0.92  ------ 
% 2.96/0.92  Current options:
% 2.96/0.92  ------ 
% 2.96/0.92  
% 2.96/0.92  ------ Input Options
% 2.96/0.92  
% 2.96/0.92  --out_options                           all
% 2.96/0.92  --tptp_safe_out                         true
% 2.96/0.92  --problem_path                          ""
% 2.96/0.92  --include_path                          ""
% 2.96/0.92  --clausifier                            res/vclausify_rel
% 2.96/0.92  --clausifier_options                    --mode clausify
% 2.96/0.92  --stdin                                 false
% 2.96/0.92  --stats_out                             all
% 2.96/0.92  
% 2.96/0.92  ------ General Options
% 2.96/0.92  
% 2.96/0.92  --fof                                   false
% 2.96/0.92  --time_out_real                         305.
% 2.96/0.92  --time_out_virtual                      -1.
% 2.96/0.92  --symbol_type_check                     false
% 2.96/0.92  --clausify_out                          false
% 2.96/0.92  --sig_cnt_out                           false
% 2.96/0.92  --trig_cnt_out                          false
% 2.96/0.92  --trig_cnt_out_tolerance                1.
% 2.96/0.92  --trig_cnt_out_sk_spl                   false
% 2.96/0.92  --abstr_cl_out                          false
% 2.96/0.92  
% 2.96/0.92  ------ Global Options
% 2.96/0.92  
% 2.96/0.92  --schedule                              default
% 2.96/0.92  --add_important_lit                     false
% 2.96/0.92  --prop_solver_per_cl                    1000
% 2.96/0.92  --min_unsat_core                        false
% 2.96/0.92  --soft_assumptions                      false
% 2.96/0.92  --soft_lemma_size                       3
% 2.96/0.92  --prop_impl_unit_size                   0
% 2.96/0.92  --prop_impl_unit                        []
% 2.96/0.92  --share_sel_clauses                     true
% 2.96/0.92  --reset_solvers                         false
% 2.96/0.92  --bc_imp_inh                            [conj_cone]
% 2.96/0.92  --conj_cone_tolerance                   3.
% 2.96/0.92  --extra_neg_conj                        none
% 2.96/0.92  --large_theory_mode                     true
% 2.96/0.92  --prolific_symb_bound                   200
% 2.96/0.92  --lt_threshold                          2000
% 2.96/0.92  --clause_weak_htbl                      true
% 2.96/0.92  --gc_record_bc_elim                     false
% 2.96/0.92  
% 2.96/0.92  ------ Preprocessing Options
% 2.96/0.92  
% 2.96/0.92  --preprocessing_flag                    true
% 2.96/0.92  --time_out_prep_mult                    0.1
% 2.96/0.92  --splitting_mode                        input
% 2.96/0.92  --splitting_grd                         true
% 2.96/0.92  --splitting_cvd                         false
% 2.96/0.92  --splitting_cvd_svl                     false
% 2.96/0.92  --splitting_nvd                         32
% 2.96/0.92  --sub_typing                            true
% 2.96/0.92  --prep_gs_sim                           true
% 2.96/0.92  --prep_unflatten                        true
% 2.96/0.92  --prep_res_sim                          true
% 2.96/0.92  --prep_upred                            true
% 2.96/0.92  --prep_sem_filter                       exhaustive
% 2.96/0.92  --prep_sem_filter_out                   false
% 2.96/0.92  --pred_elim                             true
% 2.96/0.92  --res_sim_input                         true
% 2.96/0.92  --eq_ax_congr_red                       true
% 2.96/0.92  --pure_diseq_elim                       true
% 2.96/0.92  --brand_transform                       false
% 2.96/0.92  --non_eq_to_eq                          false
% 2.96/0.92  --prep_def_merge                        true
% 2.96/0.92  --prep_def_merge_prop_impl              false
% 2.96/0.92  --prep_def_merge_mbd                    true
% 2.96/0.92  --prep_def_merge_tr_red                 false
% 2.96/0.92  --prep_def_merge_tr_cl                  false
% 2.96/0.92  --smt_preprocessing                     true
% 2.96/0.92  --smt_ac_axioms                         fast
% 2.96/0.92  --preprocessed_out                      false
% 2.96/0.92  --preprocessed_stats                    false
% 2.96/0.92  
% 2.96/0.92  ------ Abstraction refinement Options
% 2.96/0.92  
% 2.96/0.92  --abstr_ref                             []
% 2.96/0.92  --abstr_ref_prep                        false
% 2.96/0.92  --abstr_ref_until_sat                   false
% 2.96/0.92  --abstr_ref_sig_restrict                funpre
% 2.96/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/0.92  --abstr_ref_under                       []
% 2.96/0.92  
% 2.96/0.92  ------ SAT Options
% 2.96/0.92  
% 2.96/0.92  --sat_mode                              false
% 2.96/0.92  --sat_fm_restart_options                ""
% 2.96/0.92  --sat_gr_def                            false
% 2.96/0.92  --sat_epr_types                         true
% 2.96/0.92  --sat_non_cyclic_types                  false
% 2.96/0.92  --sat_finite_models                     false
% 2.96/0.92  --sat_fm_lemmas                         false
% 2.96/0.92  --sat_fm_prep                           false
% 2.96/0.92  --sat_fm_uc_incr                        true
% 2.96/0.92  --sat_out_model                         small
% 2.96/0.92  --sat_out_clauses                       false
% 2.96/0.92  
% 2.96/0.92  ------ QBF Options
% 2.96/0.92  
% 2.96/0.92  --qbf_mode                              false
% 2.96/0.92  --qbf_elim_univ                         false
% 2.96/0.92  --qbf_dom_inst                          none
% 2.96/0.92  --qbf_dom_pre_inst                      false
% 2.96/0.92  --qbf_sk_in                             false
% 2.96/0.92  --qbf_pred_elim                         true
% 2.96/0.92  --qbf_split                             512
% 2.96/0.92  
% 2.96/0.92  ------ BMC1 Options
% 2.96/0.92  
% 2.96/0.92  --bmc1_incremental                      false
% 2.96/0.92  --bmc1_axioms                           reachable_all
% 2.96/0.92  --bmc1_min_bound                        0
% 2.96/0.92  --bmc1_max_bound                        -1
% 2.96/0.92  --bmc1_max_bound_default                -1
% 2.96/0.92  --bmc1_symbol_reachability              true
% 2.96/0.92  --bmc1_property_lemmas                  false
% 2.96/0.92  --bmc1_k_induction                      false
% 2.96/0.92  --bmc1_non_equiv_states                 false
% 2.96/0.92  --bmc1_deadlock                         false
% 2.96/0.92  --bmc1_ucm                              false
% 2.96/0.92  --bmc1_add_unsat_core                   none
% 2.96/0.92  --bmc1_unsat_core_children              false
% 2.96/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/0.92  --bmc1_out_stat                         full
% 2.96/0.92  --bmc1_ground_init                      false
% 2.96/0.92  --bmc1_pre_inst_next_state              false
% 2.96/0.92  --bmc1_pre_inst_state                   false
% 2.96/0.92  --bmc1_pre_inst_reach_state             false
% 2.96/0.92  --bmc1_out_unsat_core                   false
% 2.96/0.92  --bmc1_aig_witness_out                  false
% 2.96/0.92  --bmc1_verbose                          false
% 2.96/0.92  --bmc1_dump_clauses_tptp                false
% 2.96/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.96/0.92  --bmc1_dump_file                        -
% 2.96/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.96/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.96/0.92  --bmc1_ucm_extend_mode                  1
% 2.96/0.92  --bmc1_ucm_init_mode                    2
% 2.96/0.92  --bmc1_ucm_cone_mode                    none
% 2.96/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.96/0.92  --bmc1_ucm_relax_model                  4
% 2.96/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.96/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/0.92  --bmc1_ucm_layered_model                none
% 2.96/0.92  --bmc1_ucm_max_lemma_size               10
% 2.96/0.92  
% 2.96/0.92  ------ AIG Options
% 2.96/0.92  
% 2.96/0.92  --aig_mode                              false
% 2.96/0.92  
% 2.96/0.92  ------ Instantiation Options
% 2.96/0.92  
% 2.96/0.92  --instantiation_flag                    true
% 2.96/0.92  --inst_sos_flag                         false
% 2.96/0.92  --inst_sos_phase                        true
% 2.96/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/0.92  --inst_lit_sel_side                     none
% 2.96/0.92  --inst_solver_per_active                1400
% 2.96/0.92  --inst_solver_calls_frac                1.
% 2.96/0.92  --inst_passive_queue_type               priority_queues
% 2.96/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/0.92  --inst_passive_queues_freq              [25;2]
% 2.96/0.92  --inst_dismatching                      true
% 2.96/0.92  --inst_eager_unprocessed_to_passive     true
% 2.96/0.92  --inst_prop_sim_given                   true
% 2.96/0.92  --inst_prop_sim_new                     false
% 2.96/0.92  --inst_subs_new                         false
% 2.96/0.92  --inst_eq_res_simp                      false
% 2.96/0.92  --inst_subs_given                       false
% 2.96/0.92  --inst_orphan_elimination               true
% 2.96/0.92  --inst_learning_loop_flag               true
% 2.96/0.92  --inst_learning_start                   3000
% 2.96/0.92  --inst_learning_factor                  2
% 2.96/0.92  --inst_start_prop_sim_after_learn       3
% 2.96/0.92  --inst_sel_renew                        solver
% 2.96/0.92  --inst_lit_activity_flag                true
% 2.96/0.92  --inst_restr_to_given                   false
% 2.96/0.92  --inst_activity_threshold               500
% 2.96/0.92  --inst_out_proof                        true
% 2.96/0.92  
% 2.96/0.92  ------ Resolution Options
% 2.96/0.92  
% 2.96/0.92  --resolution_flag                       false
% 2.96/0.92  --res_lit_sel                           adaptive
% 2.96/0.92  --res_lit_sel_side                      none
% 2.96/0.92  --res_ordering                          kbo
% 2.96/0.92  --res_to_prop_solver                    active
% 2.96/0.92  --res_prop_simpl_new                    false
% 2.96/0.92  --res_prop_simpl_given                  true
% 2.96/0.92  --res_passive_queue_type                priority_queues
% 2.96/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/0.92  --res_passive_queues_freq               [15;5]
% 2.96/0.92  --res_forward_subs                      full
% 2.96/0.92  --res_backward_subs                     full
% 2.96/0.92  --res_forward_subs_resolution           true
% 2.96/0.92  --res_backward_subs_resolution          true
% 2.96/0.92  --res_orphan_elimination                true
% 2.96/0.92  --res_time_limit                        2.
% 2.96/0.92  --res_out_proof                         true
% 2.96/0.92  
% 2.96/0.92  ------ Superposition Options
% 2.96/0.92  
% 2.96/0.92  --superposition_flag                    true
% 2.96/0.92  --sup_passive_queue_type                priority_queues
% 2.96/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.96/0.92  --demod_completeness_check              fast
% 2.96/0.92  --demod_use_ground                      true
% 2.96/0.92  --sup_to_prop_solver                    passive
% 2.96/0.92  --sup_prop_simpl_new                    true
% 2.96/0.92  --sup_prop_simpl_given                  true
% 2.96/0.92  --sup_fun_splitting                     false
% 2.96/0.92  --sup_smt_interval                      50000
% 2.96/0.92  
% 2.96/0.92  ------ Superposition Simplification Setup
% 2.96/0.92  
% 2.96/0.92  --sup_indices_passive                   []
% 2.96/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.92  --sup_full_bw                           [BwDemod]
% 2.96/0.92  --sup_immed_triv                        [TrivRules]
% 2.96/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.92  --sup_immed_bw_main                     []
% 2.96/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.92  
% 2.96/0.92  ------ Combination Options
% 2.96/0.92  
% 2.96/0.92  --comb_res_mult                         3
% 2.96/0.92  --comb_sup_mult                         2
% 2.96/0.92  --comb_inst_mult                        10
% 2.96/0.92  
% 2.96/0.92  ------ Debug Options
% 2.96/0.92  
% 2.96/0.92  --dbg_backtrace                         false
% 2.96/0.92  --dbg_dump_prop_clauses                 false
% 2.96/0.92  --dbg_dump_prop_clauses_file            -
% 2.96/0.92  --dbg_out_stat                          false
% 2.96/0.92  
% 2.96/0.92  
% 2.96/0.92  
% 2.96/0.92  
% 2.96/0.92  ------ Proving...
% 2.96/0.92  
% 2.96/0.92  
% 2.96/0.92  % SZS status Theorem for theBenchmark.p
% 2.96/0.92  
% 2.96/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 2.96/0.92  
% 2.96/0.92  fof(f11,axiom,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f30,plain,(
% 2.96/0.92    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f11])).
% 2.96/0.92  
% 2.96/0.92  fof(f61,plain,(
% 2.96/0.92    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f30])).
% 2.96/0.92  
% 2.96/0.92  fof(f15,conjecture,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f16,negated_conjecture,(
% 2.96/0.92    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 2.96/0.92    inference(negated_conjecture,[],[f15])).
% 2.96/0.92  
% 2.96/0.92  fof(f36,plain,(
% 2.96/0.92    ? [X0] : (? [X1] : ((~v1_tdlat_3(X1) & (v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f16])).
% 2.96/0.92  
% 2.96/0.92  fof(f37,plain,(
% 2.96/0.92    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 2.96/0.92    inference(flattening,[],[f36])).
% 2.96/0.92  
% 2.96/0.92  fof(f45,plain,(
% 2.96/0.92    ( ! [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) => (~v1_tdlat_3(sK1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(sK1))) )),
% 2.96/0.92    introduced(choice_axiom,[])).
% 2.96/0.92  
% 2.96/0.92  fof(f44,plain,(
% 2.96/0.92    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 2.96/0.92    introduced(choice_axiom,[])).
% 2.96/0.92  
% 2.96/0.92  fof(f46,plain,(
% 2.96/0.92    (~v1_tdlat_3(sK1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 2.96/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f45,f44])).
% 2.96/0.92  
% 2.96/0.92  fof(f69,plain,(
% 2.96/0.92    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 2.96/0.92    inference(cnf_transformation,[],[f46])).
% 2.96/0.92  
% 2.96/0.92  fof(f7,axiom,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f25,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f7])).
% 2.96/0.92  
% 2.96/0.92  fof(f40,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(nnf_transformation,[],[f25])).
% 2.96/0.92  
% 2.96/0.92  fof(f55,plain,(
% 2.96/0.92    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f40])).
% 2.96/0.92  
% 2.96/0.92  fof(f2,axiom,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f18,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f2])).
% 2.96/0.92  
% 2.96/0.92  fof(f50,plain,(
% 2.96/0.92    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f18])).
% 2.96/0.92  
% 2.96/0.92  fof(f67,plain,(
% 2.96/0.92    l1_pre_topc(sK0)),
% 2.96/0.92    inference(cnf_transformation,[],[f46])).
% 2.96/0.92  
% 2.96/0.92  fof(f6,axiom,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f24,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f6])).
% 2.96/0.92  
% 2.96/0.92  fof(f54,plain,(
% 2.96/0.92    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f24])).
% 2.96/0.92  
% 2.96/0.92  fof(f68,plain,(
% 2.96/0.92    l1_pre_topc(sK1)),
% 2.96/0.92    inference(cnf_transformation,[],[f46])).
% 2.96/0.92  
% 2.96/0.92  fof(f3,axiom,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f19,plain,(
% 2.96/0.92    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f3])).
% 2.96/0.92  
% 2.96/0.92  fof(f51,plain,(
% 2.96/0.92    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f19])).
% 2.96/0.92  
% 2.96/0.92  fof(f8,axiom,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f26,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f8])).
% 2.96/0.92  
% 2.96/0.92  fof(f57,plain,(
% 2.96/0.92    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f26])).
% 2.96/0.92  
% 2.96/0.92  fof(f10,axiom,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f29,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f10])).
% 2.96/0.92  
% 2.96/0.92  fof(f41,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(nnf_transformation,[],[f29])).
% 2.96/0.92  
% 2.96/0.92  fof(f59,plain,(
% 2.96/0.92    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f41])).
% 2.96/0.92  
% 2.96/0.92  fof(f1,axiom,(
% 2.96/0.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f38,plain,(
% 2.96/0.92    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.96/0.92    inference(nnf_transformation,[],[f1])).
% 2.96/0.92  
% 2.96/0.92  fof(f39,plain,(
% 2.96/0.92    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.96/0.92    inference(flattening,[],[f38])).
% 2.96/0.92  
% 2.96/0.92  fof(f49,plain,(
% 2.96/0.92    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f39])).
% 2.96/0.92  
% 2.96/0.92  fof(f47,plain,(
% 2.96/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.96/0.92    inference(cnf_transformation,[],[f39])).
% 2.96/0.92  
% 2.96/0.92  fof(f73,plain,(
% 2.96/0.92    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.96/0.92    inference(equality_resolution,[],[f47])).
% 2.96/0.92  
% 2.96/0.92  fof(f60,plain,(
% 2.96/0.92    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f41])).
% 2.96/0.92  
% 2.96/0.92  fof(f9,axiom,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f27,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f9])).
% 2.96/0.92  
% 2.96/0.92  fof(f28,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(flattening,[],[f27])).
% 2.96/0.92  
% 2.96/0.92  fof(f58,plain,(
% 2.96/0.92    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f28])).
% 2.96/0.92  
% 2.96/0.92  fof(f74,plain,(
% 2.96/0.92    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(equality_resolution,[],[f58])).
% 2.96/0.92  
% 2.96/0.92  fof(f12,axiom,(
% 2.96/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f31,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.96/0.92    inference(ennf_transformation,[],[f12])).
% 2.96/0.92  
% 2.96/0.92  fof(f32,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.96/0.92    inference(flattening,[],[f31])).
% 2.96/0.92  
% 2.96/0.92  fof(f42,plain,(
% 2.96/0.92    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.96/0.92    inference(nnf_transformation,[],[f32])).
% 2.96/0.92  
% 2.96/0.92  fof(f63,plain,(
% 2.96/0.92    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f42])).
% 2.96/0.92  
% 2.96/0.92  fof(f70,plain,(
% 2.96/0.92    v1_tdlat_3(sK0)),
% 2.96/0.92    inference(cnf_transformation,[],[f46])).
% 2.96/0.92  
% 2.96/0.92  fof(f13,axiom,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f33,plain,(
% 2.96/0.92    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f13])).
% 2.96/0.92  
% 2.96/0.92  fof(f34,plain,(
% 2.96/0.92    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(flattening,[],[f33])).
% 2.96/0.92  
% 2.96/0.92  fof(f64,plain,(
% 2.96/0.92    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f34])).
% 2.96/0.92  
% 2.96/0.92  fof(f4,axiom,(
% 2.96/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f17,plain,(
% 2.96/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 2.96/0.92    inference(pure_predicate_removal,[],[f4])).
% 2.96/0.92  
% 2.96/0.92  fof(f20,plain,(
% 2.96/0.92    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.96/0.92    inference(ennf_transformation,[],[f17])).
% 2.96/0.92  
% 2.96/0.92  fof(f21,plain,(
% 2.96/0.92    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.96/0.92    inference(flattening,[],[f20])).
% 2.96/0.92  
% 2.96/0.92  fof(f52,plain,(
% 2.96/0.92    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f21])).
% 2.96/0.92  
% 2.96/0.92  fof(f5,axiom,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => v2_pre_topc(X0)))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f22,plain,(
% 2.96/0.92    ! [X0] : ((v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f5])).
% 2.96/0.92  
% 2.96/0.92  fof(f23,plain,(
% 2.96/0.92    ! [X0] : (v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(flattening,[],[f22])).
% 2.96/0.92  
% 2.96/0.92  fof(f53,plain,(
% 2.96/0.92    ( ! [X0] : (v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f23])).
% 2.96/0.92  
% 2.96/0.92  fof(f14,axiom,(
% 2.96/0.92    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))))),
% 2.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.92  
% 2.96/0.92  fof(f35,plain,(
% 2.96/0.92    ! [X0] : ((v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(ennf_transformation,[],[f14])).
% 2.96/0.92  
% 2.96/0.92  fof(f43,plain,(
% 2.96/0.92    ! [X0] : (((v1_tdlat_3(X0) | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))) & (u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 2.96/0.92    inference(nnf_transformation,[],[f35])).
% 2.96/0.92  
% 2.96/0.92  fof(f66,plain,(
% 2.96/0.92    ( ! [X0] : (v1_tdlat_3(X0) | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f43])).
% 2.96/0.92  
% 2.96/0.92  fof(f71,plain,(
% 2.96/0.92    ~v1_tdlat_3(sK1)),
% 2.96/0.92    inference(cnf_transformation,[],[f46])).
% 2.96/0.92  
% 2.96/0.92  fof(f65,plain,(
% 2.96/0.92    ( ! [X0] : (u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.96/0.92    inference(cnf_transformation,[],[f43])).
% 2.96/0.92  
% 2.96/0.92  cnf(c_14,plain,
% 2.96/0.92      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.96/0.92      inference(cnf_transformation,[],[f61]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_808,plain,
% 2.96/0.92      ( m1_pre_topc(X0,X0) = iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_22,negated_conjecture,
% 2.96/0.92      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 2.96/0.92      inference(cnf_transformation,[],[f69]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_9,plain,
% 2.96/0.92      ( ~ m1_pre_topc(X0,X1)
% 2.96/0.92      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.96/0.92      | ~ l1_pre_topc(X0)
% 2.96/0.92      | ~ l1_pre_topc(X1) ),
% 2.96/0.92      inference(cnf_transformation,[],[f55]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3,plain,
% 2.96/0.92      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.96/0.92      inference(cnf_transformation,[],[f50]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_136,plain,
% 2.96/0.92      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.96/0.92      | ~ m1_pre_topc(X0,X1)
% 2.96/0.92      | ~ l1_pre_topc(X1) ),
% 2.96/0.92      inference(global_propositional_subsumption,[status(thm)],[c_9,c_3]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_137,plain,
% 2.96/0.92      ( ~ m1_pre_topc(X0,X1)
% 2.96/0.92      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.96/0.92      | ~ l1_pre_topc(X1) ),
% 2.96/0.92      inference(renaming,[status(thm)],[c_136]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_803,plain,
% 2.96/0.92      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_137]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1435,plain,
% 2.96/0.92      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_22,c_803]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_24,negated_conjecture,
% 2.96/0.92      ( l1_pre_topc(sK0) ),
% 2.96/0.92      inference(cnf_transformation,[],[f67]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_25,plain,
% 2.96/0.92      ( l1_pre_topc(sK0) = iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1504,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_1435,c_25]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1505,plain,
% 2.96/0.92      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top ),
% 2.96/0.92      inference(renaming,[status(thm)],[c_1504]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_7,plain,
% 2.96/0.92      ( m1_pre_topc(X0,X1)
% 2.96/0.92      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.96/0.92      | ~ l1_pre_topc(X1) ),
% 2.96/0.92      inference(cnf_transformation,[],[f54]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_813,plain,
% 2.96/0.92      ( m1_pre_topc(X0,X1) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1625,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK1) = iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_1505,c_813]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_23,negated_conjecture,
% 2.96/0.92      ( l1_pre_topc(sK1) ),
% 2.96/0.92      inference(cnf_transformation,[],[f68]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_26,plain,
% 2.96/0.92      ( l1_pre_topc(sK1) = iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1884,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK1) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_1625,c_26]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1885,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK1) = iProver_top ),
% 2.96/0.92      inference(renaming,[status(thm)],[c_1884]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1892,plain,
% 2.96/0.92      ( m1_pre_topc(sK0,sK1) = iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_808,c_1885]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_40,plain,
% 2.96/0.92      ( m1_pre_topc(X0,X0) = iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_42,plain,
% 2.96/0.92      ( m1_pre_topc(sK0,sK0) = iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_40]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1649,plain,
% 2.96/0.92      ( m1_pre_topc(sK0,sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK0,sK1) = iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1625]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_2080,plain,
% 2.96/0.92      ( m1_pre_topc(sK0,sK1) = iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_1892,c_25,c_26,c_42,c_1649]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_4,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.96/0.92      | ~ l1_pre_topc(X0) ),
% 2.96/0.92      inference(cnf_transformation,[],[f51]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_816,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_10,plain,
% 2.96/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.96/0.92      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 2.96/0.92      | ~ m1_pre_topc(X1,X2)
% 2.96/0.92      | ~ l1_pre_topc(X2) ),
% 2.96/0.92      inference(cnf_transformation,[],[f57]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_812,plain,
% 2.96/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 2.96/0.92      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X1,X2) != iProver_top
% 2.96/0.92      | l1_pre_topc(X2) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_2440,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_816,c_812]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_65,plain,
% 2.96/0.92      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top
% 2.96/0.92      | l1_pre_topc(X0) = iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3494,plain,
% 2.96/0.92      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.92      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_2440,c_65]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3495,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(renaming,[status(thm)],[c_3494]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3501,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,X2) != iProver_top
% 2.96/0.92      | m1_pre_topc(X2,X1) != iProver_top
% 2.96/0.92      | l1_pre_topc(X2) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_3495,c_812]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_817,plain,
% 2.96/0.92      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top
% 2.96/0.92      | l1_pre_topc(X0) = iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_4613,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X2,X1) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,X2) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(forward_subsumption_resolution,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_3501,c_817]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_4620,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_2080,c_4613]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6679,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_4620,c_26]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6680,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top ),
% 2.96/0.92      inference(renaming,[status(thm)],[c_6679]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_13,plain,
% 2.96/0.92      ( ~ v1_tops_2(X0,X1)
% 2.96/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.96/0.92      | r1_tarski(X0,u1_pre_topc(X1))
% 2.96/0.92      | ~ l1_pre_topc(X1) ),
% 2.96/0.92      inference(cnf_transformation,[],[f59]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_809,plain,
% 2.96/0.92      ( v1_tops_2(X0,X1) != iProver_top
% 2.96/0.92      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 2.96/0.92      | r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6689,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(X0),sK1) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) = iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_6680,c_809]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_7081,plain,
% 2.96/0.92      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | v1_tops_2(u1_pre_topc(X0),sK1) != iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_6689,c_26]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_7082,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(X0),sK1) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) = iProver_top ),
% 2.96/0.92      inference(renaming,[status(thm)],[c_7081]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3503,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(X0),X1) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.92      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1)) = iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_3495,c_809]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_0,plain,
% 2.96/0.92      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.96/0.92      inference(cnf_transformation,[],[f49]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_819,plain,
% 2.96/0.92      ( X0 = X1
% 2.96/0.92      | r1_tarski(X0,X1) != iProver_top
% 2.96/0.92      | r1_tarski(X1,X0) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3662,plain,
% 2.96/0.92      ( u1_pre_topc(X0) = u1_pre_topc(X1)
% 2.96/0.92      | v1_tops_2(u1_pre_topc(X1),X0) != iProver_top
% 2.96/0.92      | m1_pre_topc(X1,X0) != iProver_top
% 2.96/0.92      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1)) != iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_3503,c_819]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_7092,plain,
% 2.96/0.92      ( u1_pre_topc(X0) = u1_pre_topc(sK1)
% 2.96/0.92      | v1_tops_2(u1_pre_topc(X0),sK1) != iProver_top
% 2.96/0.92      | v1_tops_2(u1_pre_topc(sK1),X0) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK1,X0) != iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_7082,c_3662]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_7118,plain,
% 2.96/0.92      ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
% 2.96/0.92      | v1_tops_2(u1_pre_topc(sK0),sK1) != iProver_top
% 2.96/0.92      | v1_tops_2(u1_pre_topc(sK1),sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK1,sK0) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_7092]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_2,plain,
% 2.96/0.92      ( r1_tarski(X0,X0) ),
% 2.96/0.92      inference(cnf_transformation,[],[f73]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_818,plain,
% 2.96/0.92      ( r1_tarski(X0,X0) = iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_12,plain,
% 2.96/0.92      ( v1_tops_2(X0,X1)
% 2.96/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.96/0.92      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 2.96/0.92      | ~ l1_pre_topc(X1) ),
% 2.96/0.92      inference(cnf_transformation,[],[f60]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_810,plain,
% 2.96/0.92      ( v1_tops_2(X0,X1) = iProver_top
% 2.96/0.92      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 2.96/0.92      | r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6688,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(X0),sK1) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_6680,c_810]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6960,plain,
% 2.96/0.92      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | v1_tops_2(u1_pre_topc(X0),sK1) = iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_6688,c_26]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6961,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(X0),sK1) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1)) != iProver_top ),
% 2.96/0.92      inference(renaming,[status(thm)],[c_6960]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6969,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(sK1),sK1) = iProver_top
% 2.96/0.92      | m1_pre_topc(sK1,sK0) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_818,c_6961]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1009,plain,
% 2.96/0.92      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_2]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1127,plain,
% 2.96/0.92      ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1009]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1130,plain,
% 2.96/0.92      ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) = iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_1127]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1527,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(X0),X1)
% 2.96/0.92      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.96/0.92      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
% 2.96/0.92      | ~ l1_pre_topc(X1) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_12]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_2159,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(X0),sK1)
% 2.96/0.92      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.96/0.92      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
% 2.96/0.92      | ~ l1_pre_topc(sK1) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1527]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3223,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(sK1),sK1)
% 2.96/0.92      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.96/0.92      | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
% 2.96/0.92      | ~ l1_pre_topc(sK1) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_2159]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3224,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(sK1),sK1) = iProver_top
% 2.96/0.92      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 2.96/0.92      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_3223]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3347,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.96/0.92      | ~ l1_pre_topc(sK1) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_4]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3352,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_3347]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6977,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(sK1),sK1) = iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_6969,c_26,c_1130,c_3224,c_3352]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1626,plain,
% 2.96/0.92      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) = iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_22,c_813]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1653,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK0) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_1626,c_25]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1654,plain,
% 2.96/0.92      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) = iProver_top ),
% 2.96/0.92      inference(renaming,[status(thm)],[c_1653]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1662,plain,
% 2.96/0.92      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) = iProver_top
% 2.96/0.92      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_808,c_1654]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_4621,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.96/0.92      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_1662,c_4613]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1661,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK0) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK1) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_803,c_1654]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1895,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) = iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_1661,c_26]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1896,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK0) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK1) != iProver_top ),
% 2.96/0.92      inference(renaming,[status(thm)],[c_1895]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1903,plain,
% 2.96/0.92      ( m1_pre_topc(sK1,sK0) = iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_808,c_1896]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_2218,plain,
% 2.96/0.92      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_1903,c_26]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_4622,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK1) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_2218,c_4613]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_5477,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_4621,c_25,c_26,c_1625,c_1626,c_4622]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_5487,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_1505,c_5477]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_11,plain,
% 2.96/0.92      ( ~ v1_tops_2(X0,X1)
% 2.96/0.92      | v1_tops_2(X0,X2)
% 2.96/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 2.96/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.96/0.92      | ~ m1_pre_topc(X2,X1)
% 2.96/0.92      | ~ l1_pre_topc(X1) ),
% 2.96/0.92      inference(cnf_transformation,[],[f74]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_811,plain,
% 2.96/0.92      ( v1_tops_2(X0,X1) != iProver_top
% 2.96/0.92      | v1_tops_2(X0,X2) = iProver_top
% 2.96/0.92      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 2.96/0.92      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) != iProver_top
% 2.96/0.92      | m1_pre_topc(X2,X1) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_940,plain,
% 2.96/0.92      ( v1_tops_2(X0,X1) != iProver_top
% 2.96/0.92      | v1_tops_2(X0,X2) = iProver_top
% 2.96/0.92      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) != iProver_top
% 2.96/0.92      | m1_pre_topc(X2,X1) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(forward_subsumption_resolution,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_811,c_812]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6114,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(X0),X1) != iProver_top
% 2.96/0.92      | v1_tops_2(u1_pre_topc(X0),sK0) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK0,X1) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_5487,c_940]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6982,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(sK1),sK0) = iProver_top
% 2.96/0.92      | m1_pre_topc(sK0,sK1) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK1,sK0) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_6977,c_6114]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_453,plain,
% 2.96/0.92      ( X0 != X1 | k9_setfam_1(X0) = k9_setfam_1(X1) ),
% 2.96/0.92      theory(equality) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1772,plain,
% 2.96/0.92      ( X0 != u1_struct_0(sK0)
% 2.96/0.92      | k9_setfam_1(X0) = k9_setfam_1(u1_struct_0(sK0)) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_453]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3123,plain,
% 2.96/0.92      ( k9_setfam_1(u1_struct_0(X0)) = k9_setfam_1(u1_struct_0(sK0))
% 2.96/0.92      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1772]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6416,plain,
% 2.96/0.92      ( k9_setfam_1(u1_struct_0(sK1)) = k9_setfam_1(u1_struct_0(sK0))
% 2.96/0.92      | u1_struct_0(sK1) != u1_struct_0(sK0) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_3123]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_15,plain,
% 2.96/0.92      ( ~ m1_pre_topc(X0,X1)
% 2.96/0.92      | ~ m1_pre_topc(X0,X2)
% 2.96/0.92      | ~ m1_pre_topc(X2,X1)
% 2.96/0.92      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 2.96/0.92      | ~ v2_pre_topc(X1)
% 2.96/0.92      | ~ l1_pre_topc(X1) ),
% 2.96/0.92      inference(cnf_transformation,[],[f63]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_807,plain,
% 2.96/0.92      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/0.92      | m1_pre_topc(X2,X1) != iProver_top
% 2.96/0.92      | m1_pre_topc(X0,X2) != iProver_top
% 2.96/0.92      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 2.96/0.92      | v2_pre_topc(X1) != iProver_top
% 2.96/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_2329,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK1,X0) != iProver_top
% 2.96/0.92      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
% 2.96/0.92      | v2_pre_topc(sK0) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_2218,c_807]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_21,negated_conjecture,
% 2.96/0.92      ( v1_tdlat_3(sK0) ),
% 2.96/0.92      inference(cnf_transformation,[],[f70]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_27,plain,
% 2.96/0.92      ( v1_tdlat_3(sK0) = iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_17,plain,
% 2.96/0.92      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 2.96/0.92      inference(cnf_transformation,[],[f64]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_33,plain,
% 2.96/0.92      ( v1_tdlat_3(X0) != iProver_top
% 2.96/0.92      | v2_pre_topc(X0) = iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_35,plain,
% 2.96/0.92      ( v1_tdlat_3(sK0) != iProver_top
% 2.96/0.92      | v2_pre_topc(sK0) = iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_33]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_4079,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK1,X0) != iProver_top
% 2.96/0.92      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_2329,c_25,c_27,c_35]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_2327,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK0,X0) != iProver_top
% 2.96/0.92      | r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) = iProver_top
% 2.96/0.92      | v2_pre_topc(sK1) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_2080,c_807]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_5,plain,
% 2.96/0.92      ( ~ v2_pre_topc(X0)
% 2.96/0.92      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.96/0.92      | ~ l1_pre_topc(X0) ),
% 2.96/0.92      inference(cnf_transformation,[],[f52]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_815,plain,
% 2.96/0.92      ( v2_pre_topc(X0) != iProver_top
% 2.96/0.92      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1351,plain,
% 2.96/0.92      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.96/0.92      | v2_pre_topc(sK0) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_22,c_815]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1361,plain,
% 2.96/0.92      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_1351,c_25,c_27,c_35]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_6,plain,
% 2.96/0.92      ( v2_pre_topc(X0)
% 2.96/0.92      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.96/0.92      | ~ l1_pre_topc(X0) ),
% 2.96/0.92      inference(cnf_transformation,[],[f53]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_814,plain,
% 2.96/0.92      ( v2_pre_topc(X0) = iProver_top
% 2.96/0.92      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1366,plain,
% 2.96/0.92      ( v2_pre_topc(sK1) = iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_1361,c_814]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3956,plain,
% 2.96/0.92      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK0,X0) != iProver_top
% 2.96/0.92      | r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) = iProver_top ),
% 2.96/0.92      inference(global_propositional_subsumption,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_2327,c_26,c_1366]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3965,plain,
% 2.96/0.92      ( u1_struct_0(X0) = u1_struct_0(sK0)
% 2.96/0.92      | m1_pre_topc(X0,sK1) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK0,X0) != iProver_top
% 2.96/0.92      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK0)) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_3956,c_819]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_4449,plain,
% 2.96/0.92      ( u1_struct_0(sK1) = u1_struct_0(sK0)
% 2.96/0.92      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK0,sK1) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK1,sK0) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK1,sK1) != iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_4079,c_3965]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1005,plain,
% 2.96/0.92      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.96/0.92      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.96/0.92      | ~ m1_pre_topc(X0,X1)
% 2.96/0.92      | ~ l1_pre_topc(X1) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_10]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3318,plain,
% 2.96/0.92      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.96/0.92      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.96/0.92      | ~ m1_pre_topc(X0,sK1)
% 2.96/0.92      | ~ l1_pre_topc(sK1) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1005]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3319,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 2.96/0.92      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(X0,sK1) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_3318]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_3321,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.96/0.92      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 2.96/0.92      | m1_pre_topc(sK0,sK1) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_3319]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_2224,plain,
% 2.96/0.92      ( m1_pre_topc(sK1,sK1) = iProver_top ),
% 2.96/0.92      inference(superposition,[status(thm)],[c_2218,c_1885]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1065,plain,
% 2.96/0.92      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 2.96/0.92      | v1_tops_2(u1_pre_topc(X0),X1)
% 2.96/0.92      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.96/0.92      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.96/0.92      | ~ m1_pre_topc(X1,X0)
% 2.96/0.92      | ~ l1_pre_topc(X0) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_11]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1906,plain,
% 2.96/0.92      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 2.96/0.92      | v1_tops_2(u1_pre_topc(X0),sK1)
% 2.96/0.92      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.96/0.92      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.96/0.92      | ~ m1_pre_topc(sK1,X0)
% 2.96/0.92      | ~ l1_pre_topc(X0) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1065]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1907,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(X0),X0) != iProver_top
% 2.96/0.92      | v1_tops_2(u1_pre_topc(X0),sK1) = iProver_top
% 2.96/0.92      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 2.96/0.92      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK1,X0) != iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_1906]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1909,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(sK0),sK0) != iProver_top
% 2.96/0.92      | v1_tops_2(u1_pre_topc(sK0),sK1) = iProver_top
% 2.96/0.92      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.96/0.92      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 2.96/0.92      | m1_pre_topc(sK1,sK0) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1907]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_443,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1001,plain,
% 2.96/0.92      ( k9_setfam_1(u1_struct_0(sK1)) != X0
% 2.96/0.92      | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1)
% 2.96/0.92      | u1_pre_topc(sK1) != X0 ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_443]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1694,plain,
% 2.96/0.92      ( k9_setfam_1(u1_struct_0(sK1)) != k9_setfam_1(u1_struct_0(sK0))
% 2.96/0.92      | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1)
% 2.96/0.92      | u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK0)) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1001]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1079,plain,
% 2.96/0.92      ( X0 != X1 | u1_pre_topc(X2) != X1 | u1_pre_topc(X2) = X0 ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_443]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1248,plain,
% 2.96/0.92      ( X0 != u1_pre_topc(X1)
% 2.96/0.92      | u1_pre_topc(X2) = X0
% 2.96/0.92      | u1_pre_topc(X2) != u1_pre_topc(X1) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1079]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1474,plain,
% 2.96/0.92      ( k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
% 2.96/0.92      | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(sK0))
% 2.96/0.92      | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1248]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1693,plain,
% 2.96/0.92      ( k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
% 2.96/0.92      | u1_pre_topc(sK1) = k9_setfam_1(u1_struct_0(sK0))
% 2.96/0.92      | u1_pre_topc(sK1) != u1_pre_topc(sK0) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1474]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1042,plain,
% 2.96/0.92      ( X0 != X1 | u1_pre_topc(sK1) != X1 | u1_pre_topc(sK1) = X0 ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_443]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1163,plain,
% 2.96/0.92      ( X0 != u1_pre_topc(sK1)
% 2.96/0.92      | u1_pre_topc(sK1) = X0
% 2.96/0.92      | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1042]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1232,plain,
% 2.96/0.92      ( u1_pre_topc(X0) != u1_pre_topc(sK1)
% 2.96/0.92      | u1_pre_topc(sK1) = u1_pre_topc(X0)
% 2.96/0.92      | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1163]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1234,plain,
% 2.96/0.92      ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
% 2.96/0.92      | u1_pre_topc(sK1) = u1_pre_topc(sK0)
% 2.96/0.92      | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1232]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_442,plain,( X0 = X0 ),theory(equality) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1121,plain,
% 2.96/0.92      ( sK1 = sK1 ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_442]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_447,plain,
% 2.96/0.92      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 2.96/0.92      theory(equality) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1044,plain,
% 2.96/0.92      ( u1_pre_topc(sK1) = u1_pre_topc(X0) | sK1 != X0 ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_447]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1120,plain,
% 2.96/0.92      ( u1_pre_topc(sK1) = u1_pre_topc(sK1) | sK1 != sK1 ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1044]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1014,plain,
% 2.96/0.92      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) = iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_1009]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1016,plain,
% 2.96/0.92      ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) = iProver_top ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1014]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1008,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(X0),X0)
% 2.96/0.92      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.96/0.92      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
% 2.96/0.92      | ~ l1_pre_topc(X0) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_12]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1010,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(X0),X0) = iProver_top
% 2.96/0.92      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 2.96/0.92      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) != iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_1012,plain,
% 2.96/0.92      ( v1_tops_2(u1_pre_topc(sK0),sK0) = iProver_top
% 2.96/0.92      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.96/0.92      | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) != iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_1010]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_18,plain,
% 2.96/0.92      ( v1_tdlat_3(X0)
% 2.96/0.92      | ~ l1_pre_topc(X0)
% 2.96/0.92      | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0) ),
% 2.96/0.92      inference(cnf_transformation,[],[f66]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_20,negated_conjecture,
% 2.96/0.92      ( ~ v1_tdlat_3(sK1) ),
% 2.96/0.92      inference(cnf_transformation,[],[f71]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_272,plain,
% 2.96/0.92      ( ~ l1_pre_topc(X0)
% 2.96/0.92      | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0)
% 2.96/0.92      | sK1 != X0 ),
% 2.96/0.92      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_273,plain,
% 2.96/0.92      ( ~ l1_pre_topc(sK1)
% 2.96/0.92      | k9_setfam_1(u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
% 2.96/0.92      inference(unflattening,[status(thm)],[c_272]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_62,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.96/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.96/0.92      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_64,plain,
% 2.96/0.92      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.96/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_62]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_19,plain,
% 2.96/0.92      ( ~ v1_tdlat_3(X0)
% 2.96/0.92      | ~ l1_pre_topc(X0)
% 2.96/0.92      | k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) ),
% 2.96/0.92      inference(cnf_transformation,[],[f65]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(c_30,plain,
% 2.96/0.92      ( ~ v1_tdlat_3(sK0)
% 2.96/0.92      | ~ l1_pre_topc(sK0)
% 2.96/0.92      | k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
% 2.96/0.92      inference(instantiation,[status(thm)],[c_19]) ).
% 2.96/0.92  
% 2.96/0.92  cnf(contradiction,plain,
% 2.96/0.92      ( $false ),
% 2.96/0.92      inference(minisat,
% 2.96/0.92                [status(thm)],
% 2.96/0.92                [c_7118,c_6982,c_6416,c_4449,c_3321,c_2224,c_1909,c_1903,
% 2.96/0.92                 c_1694,c_1693,c_1649,c_1234,c_1121,c_1120,c_1016,c_1012,
% 2.96/0.92                 c_273,c_64,c_42,c_30,c_21,c_26,c_23,c_25,c_24]) ).
% 2.96/0.92  
% 2.96/0.92  
% 2.96/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 2.96/0.92  
% 2.96/0.92  ------                               Statistics
% 2.96/0.92  
% 2.96/0.92  ------ General
% 2.96/0.92  
% 2.96/0.92  abstr_ref_over_cycles:                  0
% 2.96/0.92  abstr_ref_under_cycles:                 0
% 2.96/0.92  gc_basic_clause_elim:                   0
% 2.96/0.92  forced_gc_time:                         0
% 2.96/0.92  parsing_time:                           0.013
% 2.96/0.92  unif_index_cands_time:                  0.
% 2.96/0.92  unif_index_add_time:                    0.
% 2.96/0.92  orderings_time:                         0.
% 2.96/0.92  out_proof_time:                         0.015
% 2.96/0.92  total_time:                             0.261
% 2.96/0.92  num_of_symbols:                         45
% 2.96/0.92  num_of_terms:                           2500
% 2.96/0.92  
% 2.96/0.92  ------ Preprocessing
% 2.96/0.92  
% 2.96/0.92  num_of_splits:                          0
% 2.96/0.92  num_of_split_atoms:                     0
% 2.96/0.92  num_of_reused_defs:                     0
% 2.96/0.92  num_eq_ax_congr_red:                    9
% 2.96/0.92  num_of_sem_filtered_clauses:            1
% 2.96/0.92  num_of_subtypes:                        0
% 2.96/0.92  monotx_restored_types:                  0
% 2.96/0.92  sat_num_of_epr_types:                   0
% 2.96/0.92  sat_num_of_non_cyclic_types:            0
% 2.96/0.92  sat_guarded_non_collapsed_types:        0
% 2.96/0.92  num_pure_diseq_elim:                    0
% 2.96/0.92  simp_replaced_by:                       0
% 2.96/0.92  res_preprocessed:                       117
% 2.96/0.92  prep_upred:                             0
% 2.96/0.92  prep_unflattend:                        3
% 2.96/0.92  smt_new_axioms:                         0
% 2.96/0.92  pred_elim_cands:                        6
% 2.96/0.92  pred_elim:                              1
% 2.96/0.92  pred_elim_cl:                           0
% 2.96/0.92  pred_elim_cycles:                       3
% 2.96/0.92  merged_defs:                            0
% 2.96/0.92  merged_defs_ncl:                        0
% 2.96/0.92  bin_hyper_res:                          0
% 2.96/0.92  prep_cycles:                            4
% 2.96/0.92  pred_elim_time:                         0.002
% 2.96/0.92  splitting_time:                         0.
% 2.96/0.92  sem_filter_time:                        0.
% 2.96/0.92  monotx_time:                            0.
% 2.96/0.92  subtype_inf_time:                       0.
% 2.96/0.92  
% 2.96/0.92  ------ Problem properties
% 2.96/0.92  
% 2.96/0.92  clauses:                                23
% 2.96/0.92  conjectures:                            3
% 2.96/0.92  epr:                                    8
% 2.96/0.92  horn:                                   23
% 2.96/0.92  ground:                                 7
% 2.96/0.92  unary:                                  8
% 2.96/0.92  binary:                                 2
% 2.96/0.92  lits:                                   63
% 2.96/0.92  lits_eq:                                6
% 2.96/0.92  fd_pure:                                0
% 2.96/0.92  fd_pseudo:                              0
% 2.96/0.92  fd_cond:                                0
% 2.96/0.92  fd_pseudo_cond:                         1
% 2.96/0.92  ac_symbols:                             0
% 2.96/0.92  
% 2.96/0.92  ------ Propositional Solver
% 2.96/0.92  
% 2.96/0.92  prop_solver_calls:                      30
% 2.96/0.92  prop_fast_solver_calls:                 1127
% 2.96/0.92  smt_solver_calls:                       0
% 2.96/0.92  smt_fast_solver_calls:                  0
% 2.96/0.92  prop_num_of_clauses:                    1531
% 2.96/0.92  prop_preprocess_simplified:             5644
% 2.96/0.92  prop_fo_subsumed:                       90
% 2.96/0.92  prop_solver_time:                       0.
% 2.96/0.92  smt_solver_time:                        0.
% 2.96/0.92  smt_fast_solver_time:                   0.
% 2.96/0.92  prop_fast_solver_time:                  0.
% 2.96/0.92  prop_unsat_core_time:                   0.
% 2.96/0.92  
% 2.96/0.92  ------ QBF
% 2.96/0.92  
% 2.96/0.92  qbf_q_res:                              0
% 2.96/0.92  qbf_num_tautologies:                    0
% 2.96/0.92  qbf_prep_cycles:                        0
% 2.96/0.92  
% 2.96/0.92  ------ BMC1
% 2.96/0.92  
% 2.96/0.92  bmc1_current_bound:                     -1
% 2.96/0.92  bmc1_last_solved_bound:                 -1
% 2.96/0.92  bmc1_unsat_core_size:                   -1
% 2.96/0.92  bmc1_unsat_core_parents_size:           -1
% 2.96/0.92  bmc1_merge_next_fun:                    0
% 2.96/0.92  bmc1_unsat_core_clauses_time:           0.
% 2.96/0.92  
% 2.96/0.92  ------ Instantiation
% 2.96/0.92  
% 2.96/0.92  inst_num_of_clauses:                    504
% 2.96/0.92  inst_num_in_passive:                    66
% 2.96/0.92  inst_num_in_active:                     407
% 2.96/0.92  inst_num_in_unprocessed:                31
% 2.96/0.92  inst_num_of_loops:                      430
% 2.96/0.92  inst_num_of_learning_restarts:          0
% 2.96/0.92  inst_num_moves_active_passive:          16
% 2.96/0.92  inst_lit_activity:                      0
% 2.96/0.92  inst_lit_activity_moves:                0
% 2.96/0.92  inst_num_tautologies:                   0
% 2.96/0.92  inst_num_prop_implied:                  0
% 2.96/0.92  inst_num_existing_simplified:           0
% 2.96/0.92  inst_num_eq_res_simplified:             0
% 2.96/0.92  inst_num_child_elim:                    0
% 2.96/0.92  inst_num_of_dismatching_blockings:      497
% 2.96/0.92  inst_num_of_non_proper_insts:           1195
% 2.96/0.92  inst_num_of_duplicates:                 0
% 2.96/0.92  inst_inst_num_from_inst_to_res:         0
% 2.96/0.92  inst_dismatching_checking_time:         0.
% 2.96/0.92  
% 2.96/0.92  ------ Resolution
% 2.96/0.92  
% 2.96/0.92  res_num_of_clauses:                     0
% 2.96/0.92  res_num_in_passive:                     0
% 2.96/0.92  res_num_in_active:                      0
% 2.96/0.92  res_num_of_loops:                       121
% 2.96/0.92  res_forward_subset_subsumed:            227
% 2.96/0.92  res_backward_subset_subsumed:           2
% 2.96/0.92  res_forward_subsumed:                   0
% 2.96/0.92  res_backward_subsumed:                  0
% 2.96/0.92  res_forward_subsumption_resolution:     0
% 2.96/0.92  res_backward_subsumption_resolution:    0
% 2.96/0.92  res_clause_to_clause_subsumption:       863
% 2.96/0.92  res_orphan_elimination:                 0
% 2.96/0.92  res_tautology_del:                      131
% 2.96/0.92  res_num_eq_res_simplified:              0
% 2.96/0.92  res_num_sel_changes:                    0
% 2.96/0.92  res_moves_from_active_to_pass:          0
% 2.96/0.92  
% 2.96/0.92  ------ Superposition
% 2.96/0.92  
% 2.96/0.92  sup_time_total:                         0.
% 2.96/0.92  sup_time_generating:                    0.
% 2.96/0.92  sup_time_sim_full:                      0.
% 2.96/0.92  sup_time_sim_immed:                     0.
% 2.96/0.92  
% 2.96/0.92  sup_num_of_clauses:                     135
% 2.96/0.92  sup_num_in_active:                      85
% 2.96/0.92  sup_num_in_passive:                     50
% 2.96/0.92  sup_num_of_loops:                       84
% 2.96/0.92  sup_fw_superposition:                   111
% 2.96/0.92  sup_bw_superposition:                   110
% 2.96/0.92  sup_immediate_simplified:               51
% 2.96/0.92  sup_given_eliminated:                   0
% 2.96/0.92  comparisons_done:                       0
% 2.96/0.92  comparisons_avoided:                    0
% 2.96/0.92  
% 2.96/0.92  ------ Simplifications
% 2.96/0.92  
% 2.96/0.92  
% 2.96/0.92  sim_fw_subset_subsumed:                 19
% 2.96/0.92  sim_bw_subset_subsumed:                 1
% 2.96/0.92  sim_fw_subsumed:                        27
% 2.96/0.92  sim_bw_subsumed:                        3
% 2.96/0.92  sim_fw_subsumption_res:                 2
% 2.96/0.92  sim_bw_subsumption_res:                 0
% 2.96/0.92  sim_tautology_del:                      26
% 2.96/0.92  sim_eq_tautology_del:                   9
% 2.96/0.92  sim_eq_res_simp:                        0
% 2.96/0.92  sim_fw_demodulated:                     0
% 2.96/0.92  sim_bw_demodulated:                     0
% 2.96/0.92  sim_light_normalised:                   6
% 2.96/0.92  sim_joinable_taut:                      0
% 2.96/0.92  sim_joinable_simp:                      0
% 2.96/0.92  sim_ac_normalised:                      0
% 2.96/0.92  sim_smt_subsumption:                    0
% 2.96/0.92  
%------------------------------------------------------------------------------
