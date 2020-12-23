%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:31 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 986 expanded)
%              Number of clauses        :  124 ( 355 expanded)
%              Number of leaves         :   21 ( 215 expanded)
%              Depth                    :   22
%              Number of atoms          :  661 (3958 expanded)
%              Number of equality atoms :  207 ( 935 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
     => ( ~ v2_tdlat_3(sK1)
        & v2_tdlat_3(X0)
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tdlat_3(X1)
            & v2_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ~ v2_tdlat_3(sK1)
    & v2_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f48,f47])).

fof(f73,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_838,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_141,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_3])).

cnf(c_142,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_141])).

cnf(c_832,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_843,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1679,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_843])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1706,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1679,c_26])).

cnf(c_1707,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1706])).

cnf(c_1714,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_1707])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1961,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1714,c_27])).

cnf(c_1962,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1961])).

cnf(c_1969,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_838,c_1962])).

cnf(c_2330,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1969,c_27])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_837,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_835,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_968,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_837,c_835])).

cnf(c_3271,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2330,c_968])).

cnf(c_22,negated_conjecture,
    ( v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_28,plain,
    ( v2_tdlat_3(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_34,plain,
    ( v2_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_36,plain,
    ( v2_tdlat_3(sK0) != iProver_top
    | v2_pre_topc(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_12340,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3271,c_26,c_28,c_36])).

cnf(c_1471,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_832])).

cnf(c_1536,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1471,c_26])).

cnf(c_1537,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1536])).

cnf(c_1678,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_843])).

cnf(c_1950,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1678,c_27])).

cnf(c_1951,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1950])).

cnf(c_1958,plain,
    ( m1_pre_topc(sK0,sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_838,c_1951])).

cnf(c_42,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_44,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_1702,plain,
    ( m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_2161,plain,
    ( m1_pre_topc(sK0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1958,c_26,c_27,c_44,c_1702])).

cnf(c_1554,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_835])).

cnf(c_5,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_845,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1387,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_845])).

cnf(c_2134,plain,
    ( m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1554,c_26,c_28,c_36,c_1387])).

cnf(c_2135,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2134])).

cnf(c_2166,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2161,c_2135])).

cnf(c_1480,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_3023,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2166,c_26,c_44,c_1480])).

cnf(c_3267,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK0)) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_968])).

cnf(c_1397,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1387,c_26,c_28,c_36])).

cnf(c_6,plain,
    ( v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_844,plain,
    ( v2_pre_topc(X0) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1402,plain,
    ( v2_pre_topc(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1397,c_844])).

cnf(c_3269,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK0)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2161,c_968])).

cnf(c_11497,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3267,c_27,c_1402,c_3269])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_849,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11503,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK0)
    | m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11497,c_849])).

cnf(c_12351,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | m1_pre_topc(sK0,sK1) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12340,c_11503])).

cnf(c_468,plain,
    ( X0 != X1
    | X2 != X3
    | k2_tarski(X0,X2) = k2_tarski(X1,X3) ),
    theory(equality)).

cnf(c_1840,plain,
    ( X0 != u1_struct_0(sK0)
    | X1 != k1_xboole_0
    | k2_tarski(X1,X0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_2898,plain,
    ( X0 != u1_struct_0(sK0)
    | k2_tarski(k1_xboole_0,X0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_4185,plain,
    ( k2_tarski(k1_xboole_0,u1_struct_0(X0)) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2898])).

cnf(c_9375,plain,
    ( k2_tarski(k1_xboole_0,u1_struct_0(sK1)) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4185])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1047,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8429,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_8431,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_8429])).

cnf(c_11,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1107,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6330,plain,
    ( v1_tops_2(u1_pre_topc(sK1),X0)
    | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1107])).

cnf(c_6332,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK0)
    | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_6330])).

cnf(c_4,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4168,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_13,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1360,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3848,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),X0)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_3850,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3848])).

cnf(c_3453,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_3455,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3453])).

cnf(c_12,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1595,plain,
    ( v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2260,plain,
    ( v1_tops_2(u1_pre_topc(X0),sK1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_3183,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2260])).

cnf(c_457,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2899,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_1974,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),sK1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1107])).

cnf(c_1976,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK0)
    | v1_tops_2(u1_pre_topc(sK0),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(c_1970,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1969])).

cnf(c_458,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1043,plain,
    ( k2_tarski(k1_xboole_0,u1_struct_0(sK1)) != X0
    | k2_tarski(k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_1762,plain,
    ( k2_tarski(k1_xboole_0,u1_struct_0(sK1)) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | k2_tarski(k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_1121,plain,
    ( X0 != X1
    | u1_pre_topc(X2) != X1
    | u1_pre_topc(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_1290,plain,
    ( X0 != u1_pre_topc(X1)
    | u1_pre_topc(X2) = X0
    | u1_pre_topc(X2) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_1516,plain,
    ( k2_tarski(k1_xboole_0,u1_struct_0(sK0)) != u1_pre_topc(sK0)
    | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_1761,plain,
    ( k2_tarski(k1_xboole_0,u1_struct_0(sK0)) != u1_pre_topc(sK0)
    | u1_pre_topc(sK1) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | u1_pre_topc(sK1) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_1701,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1678])).

cnf(c_1703,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_1078,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(sK1))
    | ~ r1_tarski(u1_pre_topc(sK1),X0)
    | u1_pre_topc(sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1607,plain,
    ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0))
    | u1_pre_topc(sK1) = u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_1613,plain,
    ( ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK1) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_1606,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),sK1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_1609,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1606])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1050,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1177,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_1051,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1057,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_1053,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_19,plain,
    ( v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k2_tarski(k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_21,negated_conjecture,
    ( ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_281,plain,
    ( ~ l1_pre_topc(X0)
    | k2_tarski(k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_282,plain,
    ( ~ l1_pre_topc(sK1)
    | k2_tarski(k1_xboole_0,u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_65,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_43,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_20,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | k2_tarski(k1_xboole_0,u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12351,c_9375,c_8431,c_6332,c_4168,c_3850,c_3455,c_3183,c_2899,c_1976,c_1970,c_1969,c_1762,c_1761,c_1703,c_1702,c_1613,c_1609,c_1177,c_1057,c_1053,c_282,c_65,c_44,c_43,c_31,c_22,c_27,c_24,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.14/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/0.98  
% 3.14/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/0.98  
% 3.14/0.98  ------  iProver source info
% 3.14/0.98  
% 3.14/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.14/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/0.98  git: non_committed_changes: false
% 3.14/0.98  git: last_make_outside_of_git: false
% 3.14/0.98  
% 3.14/0.98  ------ 
% 3.14/0.98  
% 3.14/0.98  ------ Input Options
% 3.14/0.98  
% 3.14/0.98  --out_options                           all
% 3.14/0.98  --tptp_safe_out                         true
% 3.14/0.98  --problem_path                          ""
% 3.14/0.98  --include_path                          ""
% 3.14/0.98  --clausifier                            res/vclausify_rel
% 3.14/0.98  --clausifier_options                    --mode clausify
% 3.14/0.98  --stdin                                 false
% 3.14/0.98  --stats_out                             all
% 3.14/0.98  
% 3.14/0.98  ------ General Options
% 3.14/0.98  
% 3.14/0.98  --fof                                   false
% 3.14/0.98  --time_out_real                         305.
% 3.14/0.98  --time_out_virtual                      -1.
% 3.14/0.98  --symbol_type_check                     false
% 3.14/0.98  --clausify_out                          false
% 3.14/0.98  --sig_cnt_out                           false
% 3.14/0.98  --trig_cnt_out                          false
% 3.14/0.98  --trig_cnt_out_tolerance                1.
% 3.14/0.98  --trig_cnt_out_sk_spl                   false
% 3.14/0.98  --abstr_cl_out                          false
% 3.14/0.98  
% 3.14/0.98  ------ Global Options
% 3.14/0.98  
% 3.14/0.98  --schedule                              default
% 3.14/0.98  --add_important_lit                     false
% 3.14/0.98  --prop_solver_per_cl                    1000
% 3.14/0.98  --min_unsat_core                        false
% 3.14/0.98  --soft_assumptions                      false
% 3.14/0.98  --soft_lemma_size                       3
% 3.14/0.98  --prop_impl_unit_size                   0
% 3.14/0.98  --prop_impl_unit                        []
% 3.14/0.98  --share_sel_clauses                     true
% 3.14/0.98  --reset_solvers                         false
% 3.14/0.98  --bc_imp_inh                            [conj_cone]
% 3.14/0.98  --conj_cone_tolerance                   3.
% 3.14/0.98  --extra_neg_conj                        none
% 3.14/0.98  --large_theory_mode                     true
% 3.14/0.98  --prolific_symb_bound                   200
% 3.14/0.98  --lt_threshold                          2000
% 3.14/0.98  --clause_weak_htbl                      true
% 3.14/0.98  --gc_record_bc_elim                     false
% 3.14/0.98  
% 3.14/0.98  ------ Preprocessing Options
% 3.14/0.98  
% 3.14/0.98  --preprocessing_flag                    true
% 3.14/0.98  --time_out_prep_mult                    0.1
% 3.14/0.98  --splitting_mode                        input
% 3.14/0.98  --splitting_grd                         true
% 3.14/0.98  --splitting_cvd                         false
% 3.14/0.98  --splitting_cvd_svl                     false
% 3.14/0.98  --splitting_nvd                         32
% 3.14/0.98  --sub_typing                            true
% 3.14/0.98  --prep_gs_sim                           true
% 3.14/0.98  --prep_unflatten                        true
% 3.14/0.98  --prep_res_sim                          true
% 3.14/0.98  --prep_upred                            true
% 3.14/0.98  --prep_sem_filter                       exhaustive
% 3.14/0.98  --prep_sem_filter_out                   false
% 3.14/0.98  --pred_elim                             true
% 3.14/0.98  --res_sim_input                         true
% 3.14/0.98  --eq_ax_congr_red                       true
% 3.14/0.98  --pure_diseq_elim                       true
% 3.14/0.98  --brand_transform                       false
% 3.14/0.98  --non_eq_to_eq                          false
% 3.14/0.98  --prep_def_merge                        true
% 3.14/0.98  --prep_def_merge_prop_impl              false
% 3.14/0.98  --prep_def_merge_mbd                    true
% 3.14/0.98  --prep_def_merge_tr_red                 false
% 3.14/0.98  --prep_def_merge_tr_cl                  false
% 3.14/0.98  --smt_preprocessing                     true
% 3.14/0.98  --smt_ac_axioms                         fast
% 3.14/0.98  --preprocessed_out                      false
% 3.14/0.98  --preprocessed_stats                    false
% 3.14/0.98  
% 3.14/0.98  ------ Abstraction refinement Options
% 3.14/0.98  
% 3.14/0.98  --abstr_ref                             []
% 3.14/0.98  --abstr_ref_prep                        false
% 3.14/0.98  --abstr_ref_until_sat                   false
% 3.14/0.98  --abstr_ref_sig_restrict                funpre
% 3.14/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.98  --abstr_ref_under                       []
% 3.14/0.98  
% 3.14/0.98  ------ SAT Options
% 3.14/0.98  
% 3.14/0.98  --sat_mode                              false
% 3.14/0.98  --sat_fm_restart_options                ""
% 3.14/0.98  --sat_gr_def                            false
% 3.14/0.98  --sat_epr_types                         true
% 3.14/0.98  --sat_non_cyclic_types                  false
% 3.14/0.98  --sat_finite_models                     false
% 3.14/0.98  --sat_fm_lemmas                         false
% 3.14/0.98  --sat_fm_prep                           false
% 3.14/0.98  --sat_fm_uc_incr                        true
% 3.14/0.98  --sat_out_model                         small
% 3.14/0.98  --sat_out_clauses                       false
% 3.14/0.98  
% 3.14/0.98  ------ QBF Options
% 3.14/0.98  
% 3.14/0.98  --qbf_mode                              false
% 3.14/0.98  --qbf_elim_univ                         false
% 3.14/0.98  --qbf_dom_inst                          none
% 3.14/0.98  --qbf_dom_pre_inst                      false
% 3.14/0.98  --qbf_sk_in                             false
% 3.14/0.98  --qbf_pred_elim                         true
% 3.14/0.98  --qbf_split                             512
% 3.14/0.98  
% 3.14/0.98  ------ BMC1 Options
% 3.14/0.98  
% 3.14/0.98  --bmc1_incremental                      false
% 3.14/0.98  --bmc1_axioms                           reachable_all
% 3.14/0.98  --bmc1_min_bound                        0
% 3.14/0.98  --bmc1_max_bound                        -1
% 3.14/0.98  --bmc1_max_bound_default                -1
% 3.14/0.98  --bmc1_symbol_reachability              true
% 3.14/0.98  --bmc1_property_lemmas                  false
% 3.14/0.98  --bmc1_k_induction                      false
% 3.14/0.98  --bmc1_non_equiv_states                 false
% 3.14/0.98  --bmc1_deadlock                         false
% 3.14/0.98  --bmc1_ucm                              false
% 3.14/0.98  --bmc1_add_unsat_core                   none
% 3.14/0.98  --bmc1_unsat_core_children              false
% 3.14/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.98  --bmc1_out_stat                         full
% 3.14/0.98  --bmc1_ground_init                      false
% 3.14/0.98  --bmc1_pre_inst_next_state              false
% 3.14/0.98  --bmc1_pre_inst_state                   false
% 3.14/0.98  --bmc1_pre_inst_reach_state             false
% 3.14/0.98  --bmc1_out_unsat_core                   false
% 3.14/0.98  --bmc1_aig_witness_out                  false
% 3.14/0.98  --bmc1_verbose                          false
% 3.14/0.98  --bmc1_dump_clauses_tptp                false
% 3.14/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.98  --bmc1_dump_file                        -
% 3.14/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.98  --bmc1_ucm_extend_mode                  1
% 3.14/0.98  --bmc1_ucm_init_mode                    2
% 3.14/0.98  --bmc1_ucm_cone_mode                    none
% 3.14/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.98  --bmc1_ucm_relax_model                  4
% 3.14/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.98  --bmc1_ucm_layered_model                none
% 3.14/0.98  --bmc1_ucm_max_lemma_size               10
% 3.14/0.98  
% 3.14/0.98  ------ AIG Options
% 3.14/0.98  
% 3.14/0.98  --aig_mode                              false
% 3.14/0.98  
% 3.14/0.98  ------ Instantiation Options
% 3.14/0.98  
% 3.14/0.98  --instantiation_flag                    true
% 3.14/0.98  --inst_sos_flag                         false
% 3.14/0.98  --inst_sos_phase                        true
% 3.14/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.98  --inst_lit_sel_side                     num_symb
% 3.14/0.98  --inst_solver_per_active                1400
% 3.14/0.98  --inst_solver_calls_frac                1.
% 3.14/0.98  --inst_passive_queue_type               priority_queues
% 3.14/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.98  --inst_passive_queues_freq              [25;2]
% 3.14/0.98  --inst_dismatching                      true
% 3.14/0.98  --inst_eager_unprocessed_to_passive     true
% 3.14/0.98  --inst_prop_sim_given                   true
% 3.14/0.98  --inst_prop_sim_new                     false
% 3.14/0.98  --inst_subs_new                         false
% 3.14/0.98  --inst_eq_res_simp                      false
% 3.14/0.98  --inst_subs_given                       false
% 3.14/0.98  --inst_orphan_elimination               true
% 3.14/0.98  --inst_learning_loop_flag               true
% 3.14/0.98  --inst_learning_start                   3000
% 3.14/0.98  --inst_learning_factor                  2
% 3.14/0.98  --inst_start_prop_sim_after_learn       3
% 3.14/0.98  --inst_sel_renew                        solver
% 3.14/0.98  --inst_lit_activity_flag                true
% 3.14/0.98  --inst_restr_to_given                   false
% 3.14/0.98  --inst_activity_threshold               500
% 3.14/0.98  --inst_out_proof                        true
% 3.14/0.98  
% 3.14/0.98  ------ Resolution Options
% 3.14/0.98  
% 3.14/0.98  --resolution_flag                       true
% 3.14/0.98  --res_lit_sel                           adaptive
% 3.14/0.98  --res_lit_sel_side                      none
% 3.14/0.98  --res_ordering                          kbo
% 3.14/0.98  --res_to_prop_solver                    active
% 3.14/0.98  --res_prop_simpl_new                    false
% 3.14/0.98  --res_prop_simpl_given                  true
% 3.14/0.98  --res_passive_queue_type                priority_queues
% 3.14/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.98  --res_passive_queues_freq               [15;5]
% 3.14/0.98  --res_forward_subs                      full
% 3.14/0.98  --res_backward_subs                     full
% 3.14/0.98  --res_forward_subs_resolution           true
% 3.14/0.98  --res_backward_subs_resolution          true
% 3.14/0.98  --res_orphan_elimination                true
% 3.14/0.98  --res_time_limit                        2.
% 3.14/0.98  --res_out_proof                         true
% 3.14/0.98  
% 3.14/0.98  ------ Superposition Options
% 3.14/0.98  
% 3.14/0.98  --superposition_flag                    true
% 3.14/0.98  --sup_passive_queue_type                priority_queues
% 3.14/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.98  --demod_completeness_check              fast
% 3.14/0.98  --demod_use_ground                      true
% 3.14/0.98  --sup_to_prop_solver                    passive
% 3.14/0.98  --sup_prop_simpl_new                    true
% 3.14/0.98  --sup_prop_simpl_given                  true
% 3.14/0.98  --sup_fun_splitting                     false
% 3.14/0.98  --sup_smt_interval                      50000
% 3.14/0.98  
% 3.14/0.98  ------ Superposition Simplification Setup
% 3.14/0.98  
% 3.14/0.98  --sup_indices_passive                   []
% 3.14/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.98  --sup_full_bw                           [BwDemod]
% 3.14/0.98  --sup_immed_triv                        [TrivRules]
% 3.14/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.98  --sup_immed_bw_main                     []
% 3.14/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.98  
% 3.14/0.98  ------ Combination Options
% 3.14/0.98  
% 3.14/0.98  --comb_res_mult                         3
% 3.14/0.98  --comb_sup_mult                         2
% 3.14/0.98  --comb_inst_mult                        10
% 3.14/0.98  
% 3.14/0.98  ------ Debug Options
% 3.14/0.98  
% 3.14/0.98  --dbg_backtrace                         false
% 3.14/0.98  --dbg_dump_prop_clauses                 false
% 3.14/0.98  --dbg_dump_prop_clauses_file            -
% 3.14/0.98  --dbg_out_stat                          false
% 3.14/0.98  ------ Parsing...
% 3.14/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/0.98  
% 3.14/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.14/0.98  
% 3.14/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/0.98  
% 3.14/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/0.98  ------ Proving...
% 3.14/0.98  ------ Problem Properties 
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  clauses                                 24
% 3.14/0.98  conjectures                             3
% 3.14/0.98  EPR                                     9
% 3.14/0.98  Horn                                    24
% 3.14/0.98  unary                                   8
% 3.14/0.98  binary                                  2
% 3.14/0.98  lits                                    68
% 3.14/0.98  lits eq                                 6
% 3.14/0.98  fd_pure                                 0
% 3.14/0.98  fd_pseudo                               0
% 3.14/0.98  fd_cond                                 0
% 3.14/0.98  fd_pseudo_cond                          1
% 3.14/0.98  AC symbols                              0
% 3.14/0.98  
% 3.14/0.98  ------ Schedule dynamic 5 is on 
% 3.14/0.98  
% 3.14/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  ------ 
% 3.14/0.98  Current options:
% 3.14/0.98  ------ 
% 3.14/0.98  
% 3.14/0.98  ------ Input Options
% 3.14/0.98  
% 3.14/0.98  --out_options                           all
% 3.14/0.98  --tptp_safe_out                         true
% 3.14/0.98  --problem_path                          ""
% 3.14/0.98  --include_path                          ""
% 3.14/0.98  --clausifier                            res/vclausify_rel
% 3.14/0.98  --clausifier_options                    --mode clausify
% 3.14/0.98  --stdin                                 false
% 3.14/0.98  --stats_out                             all
% 3.14/0.98  
% 3.14/0.98  ------ General Options
% 3.14/0.98  
% 3.14/0.98  --fof                                   false
% 3.14/0.98  --time_out_real                         305.
% 3.14/0.98  --time_out_virtual                      -1.
% 3.14/0.98  --symbol_type_check                     false
% 3.14/0.98  --clausify_out                          false
% 3.14/0.98  --sig_cnt_out                           false
% 3.14/0.98  --trig_cnt_out                          false
% 3.14/0.98  --trig_cnt_out_tolerance                1.
% 3.14/0.98  --trig_cnt_out_sk_spl                   false
% 3.14/0.98  --abstr_cl_out                          false
% 3.14/0.98  
% 3.14/0.98  ------ Global Options
% 3.14/0.98  
% 3.14/0.98  --schedule                              default
% 3.14/0.98  --add_important_lit                     false
% 3.14/0.98  --prop_solver_per_cl                    1000
% 3.14/0.98  --min_unsat_core                        false
% 3.14/0.98  --soft_assumptions                      false
% 3.14/0.98  --soft_lemma_size                       3
% 3.14/0.98  --prop_impl_unit_size                   0
% 3.14/0.98  --prop_impl_unit                        []
% 3.14/0.98  --share_sel_clauses                     true
% 3.14/0.98  --reset_solvers                         false
% 3.14/0.98  --bc_imp_inh                            [conj_cone]
% 3.14/0.98  --conj_cone_tolerance                   3.
% 3.14/0.98  --extra_neg_conj                        none
% 3.14/0.98  --large_theory_mode                     true
% 3.14/0.98  --prolific_symb_bound                   200
% 3.14/0.98  --lt_threshold                          2000
% 3.14/0.98  --clause_weak_htbl                      true
% 3.14/0.98  --gc_record_bc_elim                     false
% 3.14/0.98  
% 3.14/0.98  ------ Preprocessing Options
% 3.14/0.98  
% 3.14/0.98  --preprocessing_flag                    true
% 3.14/0.98  --time_out_prep_mult                    0.1
% 3.14/0.98  --splitting_mode                        input
% 3.14/0.98  --splitting_grd                         true
% 3.14/0.98  --splitting_cvd                         false
% 3.14/0.98  --splitting_cvd_svl                     false
% 3.14/0.98  --splitting_nvd                         32
% 3.14/0.98  --sub_typing                            true
% 3.14/0.98  --prep_gs_sim                           true
% 3.14/0.98  --prep_unflatten                        true
% 3.14/0.98  --prep_res_sim                          true
% 3.14/0.98  --prep_upred                            true
% 3.14/0.98  --prep_sem_filter                       exhaustive
% 3.14/0.98  --prep_sem_filter_out                   false
% 3.14/0.98  --pred_elim                             true
% 3.14/0.98  --res_sim_input                         true
% 3.14/0.98  --eq_ax_congr_red                       true
% 3.14/0.98  --pure_diseq_elim                       true
% 3.14/0.98  --brand_transform                       false
% 3.14/0.98  --non_eq_to_eq                          false
% 3.14/0.98  --prep_def_merge                        true
% 3.14/0.98  --prep_def_merge_prop_impl              false
% 3.14/0.98  --prep_def_merge_mbd                    true
% 3.14/0.98  --prep_def_merge_tr_red                 false
% 3.14/0.98  --prep_def_merge_tr_cl                  false
% 3.14/0.98  --smt_preprocessing                     true
% 3.14/0.98  --smt_ac_axioms                         fast
% 3.14/0.98  --preprocessed_out                      false
% 3.14/0.98  --preprocessed_stats                    false
% 3.14/0.98  
% 3.14/0.98  ------ Abstraction refinement Options
% 3.14/0.98  
% 3.14/0.98  --abstr_ref                             []
% 3.14/0.98  --abstr_ref_prep                        false
% 3.14/0.98  --abstr_ref_until_sat                   false
% 3.14/0.98  --abstr_ref_sig_restrict                funpre
% 3.14/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.98  --abstr_ref_under                       []
% 3.14/0.98  
% 3.14/0.98  ------ SAT Options
% 3.14/0.98  
% 3.14/0.98  --sat_mode                              false
% 3.14/0.98  --sat_fm_restart_options                ""
% 3.14/0.98  --sat_gr_def                            false
% 3.14/0.98  --sat_epr_types                         true
% 3.14/0.98  --sat_non_cyclic_types                  false
% 3.14/0.98  --sat_finite_models                     false
% 3.14/0.98  --sat_fm_lemmas                         false
% 3.14/0.98  --sat_fm_prep                           false
% 3.14/0.98  --sat_fm_uc_incr                        true
% 3.14/0.98  --sat_out_model                         small
% 3.14/0.98  --sat_out_clauses                       false
% 3.14/0.98  
% 3.14/0.98  ------ QBF Options
% 3.14/0.98  
% 3.14/0.98  --qbf_mode                              false
% 3.14/0.98  --qbf_elim_univ                         false
% 3.14/0.98  --qbf_dom_inst                          none
% 3.14/0.98  --qbf_dom_pre_inst                      false
% 3.14/0.98  --qbf_sk_in                             false
% 3.14/0.98  --qbf_pred_elim                         true
% 3.14/0.98  --qbf_split                             512
% 3.14/0.98  
% 3.14/0.98  ------ BMC1 Options
% 3.14/0.98  
% 3.14/0.98  --bmc1_incremental                      false
% 3.14/0.98  --bmc1_axioms                           reachable_all
% 3.14/0.98  --bmc1_min_bound                        0
% 3.14/0.98  --bmc1_max_bound                        -1
% 3.14/0.98  --bmc1_max_bound_default                -1
% 3.14/0.98  --bmc1_symbol_reachability              true
% 3.14/0.98  --bmc1_property_lemmas                  false
% 3.14/0.98  --bmc1_k_induction                      false
% 3.14/0.98  --bmc1_non_equiv_states                 false
% 3.14/0.98  --bmc1_deadlock                         false
% 3.14/0.98  --bmc1_ucm                              false
% 3.14/0.98  --bmc1_add_unsat_core                   none
% 3.14/0.98  --bmc1_unsat_core_children              false
% 3.14/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.98  --bmc1_out_stat                         full
% 3.14/0.98  --bmc1_ground_init                      false
% 3.14/0.98  --bmc1_pre_inst_next_state              false
% 3.14/0.98  --bmc1_pre_inst_state                   false
% 3.14/0.98  --bmc1_pre_inst_reach_state             false
% 3.14/0.98  --bmc1_out_unsat_core                   false
% 3.14/0.98  --bmc1_aig_witness_out                  false
% 3.14/0.98  --bmc1_verbose                          false
% 3.14/0.98  --bmc1_dump_clauses_tptp                false
% 3.14/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.98  --bmc1_dump_file                        -
% 3.14/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.98  --bmc1_ucm_extend_mode                  1
% 3.14/0.98  --bmc1_ucm_init_mode                    2
% 3.14/0.98  --bmc1_ucm_cone_mode                    none
% 3.14/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.98  --bmc1_ucm_relax_model                  4
% 3.14/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.98  --bmc1_ucm_layered_model                none
% 3.14/0.98  --bmc1_ucm_max_lemma_size               10
% 3.14/0.98  
% 3.14/0.98  ------ AIG Options
% 3.14/0.98  
% 3.14/0.98  --aig_mode                              false
% 3.14/0.98  
% 3.14/0.98  ------ Instantiation Options
% 3.14/0.98  
% 3.14/0.98  --instantiation_flag                    true
% 3.14/0.98  --inst_sos_flag                         false
% 3.14/0.98  --inst_sos_phase                        true
% 3.14/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.98  --inst_lit_sel_side                     none
% 3.14/0.98  --inst_solver_per_active                1400
% 3.14/0.98  --inst_solver_calls_frac                1.
% 3.14/0.98  --inst_passive_queue_type               priority_queues
% 3.14/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.98  --inst_passive_queues_freq              [25;2]
% 3.14/0.98  --inst_dismatching                      true
% 3.14/0.98  --inst_eager_unprocessed_to_passive     true
% 3.14/0.98  --inst_prop_sim_given                   true
% 3.14/0.98  --inst_prop_sim_new                     false
% 3.14/0.98  --inst_subs_new                         false
% 3.14/0.98  --inst_eq_res_simp                      false
% 3.14/0.98  --inst_subs_given                       false
% 3.14/0.98  --inst_orphan_elimination               true
% 3.14/0.98  --inst_learning_loop_flag               true
% 3.14/0.98  --inst_learning_start                   3000
% 3.14/0.98  --inst_learning_factor                  2
% 3.14/0.98  --inst_start_prop_sim_after_learn       3
% 3.14/0.98  --inst_sel_renew                        solver
% 3.14/0.98  --inst_lit_activity_flag                true
% 3.14/0.98  --inst_restr_to_given                   false
% 3.14/0.98  --inst_activity_threshold               500
% 3.14/0.98  --inst_out_proof                        true
% 3.14/0.98  
% 3.14/0.98  ------ Resolution Options
% 3.14/0.98  
% 3.14/0.98  --resolution_flag                       false
% 3.14/0.98  --res_lit_sel                           adaptive
% 3.14/0.98  --res_lit_sel_side                      none
% 3.14/0.98  --res_ordering                          kbo
% 3.14/0.98  --res_to_prop_solver                    active
% 3.14/0.98  --res_prop_simpl_new                    false
% 3.14/0.98  --res_prop_simpl_given                  true
% 3.14/0.98  --res_passive_queue_type                priority_queues
% 3.14/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.98  --res_passive_queues_freq               [15;5]
% 3.14/0.98  --res_forward_subs                      full
% 3.14/0.98  --res_backward_subs                     full
% 3.14/0.98  --res_forward_subs_resolution           true
% 3.14/0.98  --res_backward_subs_resolution          true
% 3.14/0.98  --res_orphan_elimination                true
% 3.14/0.98  --res_time_limit                        2.
% 3.14/0.98  --res_out_proof                         true
% 3.14/0.98  
% 3.14/0.98  ------ Superposition Options
% 3.14/0.98  
% 3.14/0.98  --superposition_flag                    true
% 3.14/0.98  --sup_passive_queue_type                priority_queues
% 3.14/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.98  --demod_completeness_check              fast
% 3.14/0.98  --demod_use_ground                      true
% 3.14/0.98  --sup_to_prop_solver                    passive
% 3.14/0.98  --sup_prop_simpl_new                    true
% 3.14/0.98  --sup_prop_simpl_given                  true
% 3.14/0.98  --sup_fun_splitting                     false
% 3.14/0.98  --sup_smt_interval                      50000
% 3.14/0.98  
% 3.14/0.98  ------ Superposition Simplification Setup
% 3.14/0.98  
% 3.14/0.98  --sup_indices_passive                   []
% 3.14/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.98  --sup_full_bw                           [BwDemod]
% 3.14/0.98  --sup_immed_triv                        [TrivRules]
% 3.14/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.98  --sup_immed_bw_main                     []
% 3.14/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.98  
% 3.14/0.98  ------ Combination Options
% 3.14/0.98  
% 3.14/0.98  --comb_res_mult                         3
% 3.14/0.98  --comb_sup_mult                         2
% 3.14/0.98  --comb_inst_mult                        10
% 3.14/0.98  
% 3.14/0.98  ------ Debug Options
% 3.14/0.98  
% 3.14/0.98  --dbg_backtrace                         false
% 3.14/0.98  --dbg_dump_prop_clauses                 false
% 3.14/0.98  --dbg_dump_prop_clauses_file            -
% 3.14/0.98  --dbg_out_stat                          false
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  ------ Proving...
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  % SZS status Theorem for theBenchmark.p
% 3.14/0.98  
% 3.14/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/0.98  
% 3.14/0.98  fof(f11,axiom,(
% 3.14/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.14/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.98  
% 3.14/0.98  fof(f31,plain,(
% 3.14/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.14/0.98    inference(ennf_transformation,[],[f11])).
% 3.14/0.98  
% 3.14/0.98  fof(f64,plain,(
% 3.14/0.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.14/0.98    inference(cnf_transformation,[],[f31])).
% 3.14/0.98  
% 3.14/0.98  fof(f7,axiom,(
% 3.14/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.14/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.98  
% 3.14/0.98  fof(f26,plain,(
% 3.14/0.98    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.14/0.98    inference(ennf_transformation,[],[f7])).
% 3.14/0.98  
% 3.14/0.98  fof(f43,plain,(
% 3.14/0.98    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.14/0.98    inference(nnf_transformation,[],[f26])).
% 3.14/0.98  
% 3.14/0.98  fof(f58,plain,(
% 3.14/0.98    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.14/0.98    inference(cnf_transformation,[],[f43])).
% 3.14/0.98  
% 3.14/0.98  fof(f2,axiom,(
% 3.14/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.14/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.98  
% 3.14/0.98  fof(f19,plain,(
% 3.14/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.14/0.98    inference(ennf_transformation,[],[f2])).
% 3.14/0.98  
% 3.14/0.98  fof(f53,plain,(
% 3.14/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.14/0.98    inference(cnf_transformation,[],[f19])).
% 3.14/0.98  
% 3.14/0.98  fof(f16,conjecture,(
% 3.14/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 3.14/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.98  
% 3.14/0.98  fof(f17,negated_conjecture,(
% 3.14/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 3.14/0.98    inference(negated_conjecture,[],[f16])).
% 3.14/0.98  
% 3.14/0.98  fof(f39,plain,(
% 3.14/0.98    ? [X0] : (? [X1] : ((~v2_tdlat_3(X1) & (v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.14/0.98    inference(ennf_transformation,[],[f17])).
% 3.14/0.98  
% 3.14/0.98  fof(f40,plain,(
% 3.14/0.98    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.14/0.98    inference(flattening,[],[f39])).
% 3.14/0.98  
% 3.14/0.98  fof(f48,plain,(
% 3.14/0.98    ( ! [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) => (~v2_tdlat_3(sK1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(sK1))) )),
% 3.14/0.98    introduced(choice_axiom,[])).
% 3.14/0.98  
% 3.14/0.98  fof(f47,plain,(
% 3.14/0.98    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 3.14/0.98    introduced(choice_axiom,[])).
% 3.14/0.98  
% 3.14/0.98  fof(f49,plain,(
% 3.14/0.98    (~v2_tdlat_3(sK1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 3.14/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f48,f47])).
% 3.14/0.98  
% 3.14/0.98  fof(f73,plain,(
% 3.14/0.98    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 3.14/0.98    inference(cnf_transformation,[],[f49])).
% 3.14/0.98  
% 3.14/0.98  fof(f6,axiom,(
% 3.14/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.14/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.98  
% 3.14/0.98  fof(f25,plain,(
% 3.14/0.98    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.14/0.98    inference(ennf_transformation,[],[f6])).
% 3.14/0.98  
% 3.14/0.98  fof(f57,plain,(
% 3.14/0.98    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.14/0.98    inference(cnf_transformation,[],[f25])).
% 3.14/0.98  
% 3.14/0.98  fof(f71,plain,(
% 3.14/0.98    l1_pre_topc(sK0)),
% 3.14/0.98    inference(cnf_transformation,[],[f49])).
% 3.14/0.98  
% 3.14/0.98  fof(f72,plain,(
% 3.14/0.98    l1_pre_topc(sK1)),
% 3.14/0.98    inference(cnf_transformation,[],[f49])).
% 3.14/0.98  
% 3.14/0.98  fof(f12,axiom,(
% 3.14/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.14/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.98  
% 3.14/0.98  fof(f32,plain,(
% 3.14/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.14/0.98    inference(ennf_transformation,[],[f12])).
% 3.14/0.98  
% 3.14/0.98  fof(f33,plain,(
% 3.14/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.14/0.98    inference(flattening,[],[f32])).
% 3.14/0.98  
% 3.14/0.98  fof(f45,plain,(
% 3.14/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.14/0.98    inference(nnf_transformation,[],[f33])).
% 3.14/0.98  
% 3.14/0.98  fof(f66,plain,(
% 3.14/0.98    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.98    inference(cnf_transformation,[],[f45])).
% 3.14/0.98  
% 3.14/0.98  fof(f13,axiom,(
% 3.14/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.14/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.98  
% 3.14/0.98  fof(f34,plain,(
% 3.14/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.14/0.98    inference(ennf_transformation,[],[f13])).
% 3.14/0.98  
% 3.14/0.98  fof(f35,plain,(
% 3.14/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.14/0.98    inference(flattening,[],[f34])).
% 3.14/0.98  
% 3.14/0.98  fof(f67,plain,(
% 3.14/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.98    inference(cnf_transformation,[],[f35])).
% 3.14/0.98  
% 3.14/0.98  fof(f74,plain,(
% 3.14/0.98    v2_tdlat_3(sK0)),
% 3.14/0.98    inference(cnf_transformation,[],[f49])).
% 3.14/0.98  
% 3.14/0.98  fof(f14,axiom,(
% 3.14/0.98    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.14/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.98  
% 3.14/0.98  fof(f36,plain,(
% 3.14/0.98    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.14/0.98    inference(ennf_transformation,[],[f14])).
% 3.14/0.98  
% 3.14/0.98  fof(f37,plain,(
% 3.14/0.98    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.14/0.98    inference(flattening,[],[f36])).
% 3.14/0.98  
% 3.14/0.98  fof(f68,plain,(
% 3.14/0.98    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.14/0.98    inference(cnf_transformation,[],[f37])).
% 3.14/0.98  
% 3.14/0.98  fof(f4,axiom,(
% 3.14/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.14/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.98  
% 3.14/0.98  fof(f18,plain,(
% 3.14/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.14/0.98    inference(pure_predicate_removal,[],[f4])).
% 3.14/0.98  
% 3.14/0.98  fof(f21,plain,(
% 3.14/0.98    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.14/0.98    inference(ennf_transformation,[],[f18])).
% 3.14/0.98  
% 3.14/0.98  fof(f22,plain,(
% 3.14/0.98    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.14/0.99    inference(flattening,[],[f21])).
% 3.14/0.99  
% 3.14/0.99  fof(f55,plain,(
% 3.14/0.99    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f22])).
% 3.14/0.99  
% 3.14/0.99  fof(f5,axiom,(
% 3.14/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => v2_pre_topc(X0)))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f23,plain,(
% 3.14/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f5])).
% 3.14/0.99  
% 3.14/0.99  fof(f24,plain,(
% 3.14/0.99    ! [X0] : (v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(flattening,[],[f23])).
% 3.14/0.99  
% 3.14/0.99  fof(f56,plain,(
% 3.14/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f24])).
% 3.14/0.99  
% 3.14/0.99  fof(f1,axiom,(
% 3.14/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f41,plain,(
% 3.14/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/0.99    inference(nnf_transformation,[],[f1])).
% 3.14/0.99  
% 3.14/0.99  fof(f42,plain,(
% 3.14/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/0.99    inference(flattening,[],[f41])).
% 3.14/0.99  
% 3.14/0.99  fof(f52,plain,(
% 3.14/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f42])).
% 3.14/0.99  
% 3.14/0.99  fof(f8,axiom,(
% 3.14/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f27,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f8])).
% 3.14/0.99  
% 3.14/0.99  fof(f60,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f9,axiom,(
% 3.14/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f28,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f9])).
% 3.14/0.99  
% 3.14/0.99  fof(f29,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(flattening,[],[f28])).
% 3.14/0.99  
% 3.14/0.99  fof(f61,plain,(
% 3.14/0.99    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f29])).
% 3.14/0.99  
% 3.14/0.99  fof(f78,plain,(
% 3.14/0.99    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(equality_resolution,[],[f61])).
% 3.14/0.99  
% 3.14/0.99  fof(f3,axiom,(
% 3.14/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f20,plain,(
% 3.14/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f3])).
% 3.14/0.99  
% 3.14/0.99  fof(f54,plain,(
% 3.14/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f20])).
% 3.14/0.99  
% 3.14/0.99  fof(f10,axiom,(
% 3.14/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f30,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f10])).
% 3.14/0.99  
% 3.14/0.99  fof(f44,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(nnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f62,plain,(
% 3.14/0.99    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f44])).
% 3.14/0.99  
% 3.14/0.99  fof(f63,plain,(
% 3.14/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f44])).
% 3.14/0.99  
% 3.14/0.99  fof(f50,plain,(
% 3.14/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.14/0.99    inference(cnf_transformation,[],[f42])).
% 3.14/0.99  
% 3.14/0.99  fof(f77,plain,(
% 3.14/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.14/0.99    inference(equality_resolution,[],[f50])).
% 3.14/0.99  
% 3.14/0.99  fof(f15,axiom,(
% 3.14/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f38,plain,(
% 3.14/0.99    ! [X0] : ((v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f15])).
% 3.14/0.99  
% 3.14/0.99  fof(f46,plain,(
% 3.14/0.99    ! [X0] : (((v2_tdlat_3(X0) | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))) & (u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~v2_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(nnf_transformation,[],[f38])).
% 3.14/0.99  
% 3.14/0.99  fof(f70,plain,(
% 3.14/0.99    ( ! [X0] : (v2_tdlat_3(X0) | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f46])).
% 3.14/0.99  
% 3.14/0.99  fof(f75,plain,(
% 3.14/0.99    ~v2_tdlat_3(sK1)),
% 3.14/0.99    inference(cnf_transformation,[],[f49])).
% 3.14/0.99  
% 3.14/0.99  fof(f69,plain,(
% 3.14/0.99    ( ! [X0] : (u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f46])).
% 3.14/0.99  
% 3.14/0.99  cnf(c_14,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_838,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.14/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_9,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.14/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.14/0.99      | ~ l1_pre_topc(X0)
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_141,plain,
% 3.14/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.14/0.99      | ~ m1_pre_topc(X0,X1)
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(global_propositional_subsumption,[status(thm)],[c_9,c_3]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_142,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.14/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_141]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_832,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.14/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_142]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_23,negated_conjecture,
% 3.14/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X1)
% 3.14/0.99      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_843,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X1) = iProver_top
% 3.14/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.14/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1679,plain,
% 3.14/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0,sK0) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_23,c_843]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_25,negated_conjecture,
% 3.14/0.99      ( l1_pre_topc(sK0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_26,plain,
% 3.14/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1706,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK0) = iProver_top
% 3.14/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_1679,c_26]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1707,plain,
% 3.14/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0,sK0) = iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_1706]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1714,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK0) = iProver_top
% 3.14/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_832,c_1707]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_24,negated_conjecture,
% 3.14/0.99      ( l1_pre_topc(sK1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_27,plain,
% 3.14/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1961,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0,sK0) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_1714,c_27]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1962,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK0) = iProver_top
% 3.14/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_1961]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1969,plain,
% 3.14/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_838,c_1962]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2330,plain,
% 3.14/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_1969,c_27]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_15,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.14/0.99      | ~ m1_pre_topc(X0,X2)
% 3.14/0.99      | ~ m1_pre_topc(X2,X1)
% 3.14/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.14/0.99      | ~ v2_pre_topc(X1)
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_837,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.14/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 3.14/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 3.14/0.99      | v2_pre_topc(X1) != iProver_top
% 3.14/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_17,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.14/0.99      | ~ m1_pre_topc(X2,X0)
% 3.14/0.99      | m1_pre_topc(X2,X1)
% 3.14/0.99      | ~ v2_pre_topc(X1)
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_835,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.14/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.14/0.99      | m1_pre_topc(X2,X1) = iProver_top
% 3.14/0.99      | v2_pre_topc(X1) != iProver_top
% 3.14/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_968,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.14/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.14/0.99      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
% 3.14/0.99      | v2_pre_topc(X1) != iProver_top
% 3.14/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.14/0.99      inference(forward_subsumption_resolution,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_837,c_835]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3271,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.14/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
% 3.14/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2330,c_968]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_22,negated_conjecture,
% 3.14/0.99      ( v2_tdlat_3(sK0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_28,plain,
% 3.14/0.99      ( v2_tdlat_3(sK0) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_18,plain,
% 3.14/0.99      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_34,plain,
% 3.14/0.99      ( v2_tdlat_3(X0) != iProver_top
% 3.14/0.99      | v2_pre_topc(X0) = iProver_top
% 3.14/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_36,plain,
% 3.14/0.99      ( v2_tdlat_3(sK0) != iProver_top
% 3.14/0.99      | v2_pre_topc(sK0) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_34]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_12340,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.14/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_3271,c_26,c_28,c_36]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1471,plain,
% 3.14/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.14/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_23,c_832]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1536,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_1471,c_26]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1537,plain,
% 3.14/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.14/0.99      | m1_pre_topc(X0,sK0) != iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_1536]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1678,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0,sK1) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1537,c_843]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1950,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK1) = iProver_top
% 3.14/0.99      | m1_pre_topc(X0,sK0) != iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_1678,c_27]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1951,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0,sK1) = iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_1950]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1958,plain,
% 3.14/0.99      ( m1_pre_topc(sK0,sK1) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_838,c_1951]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_42,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.14/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_44,plain,
% 3.14/0.99      ( m1_pre_topc(sK0,sK0) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_42]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1702,plain,
% 3.14/0.99      ( m1_pre_topc(sK0,sK0) != iProver_top
% 3.14/0.99      | m1_pre_topc(sK0,sK1) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1678]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2161,plain,
% 3.14/0.99      ( m1_pre_topc(sK0,sK1) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_1958,c_26,c_27,c_44,c_1702]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1554,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.14/0.99      | m1_pre_topc(X1,sK0) != iProver_top
% 3.14/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.14/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1537,c_835]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5,plain,
% 3.14/0.99      ( ~ v2_pre_topc(X0)
% 3.14/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.14/0.99      | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_845,plain,
% 3.14/0.99      ( v2_pre_topc(X0) != iProver_top
% 3.14/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 3.14/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1387,plain,
% 3.14/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.14/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_23,c_845]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2134,plain,
% 3.14/0.99      ( m1_pre_topc(X1,sK0) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.14/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.14/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_1554,c_26,c_28,c_36,c_1387]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2135,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.14/0.99      | m1_pre_topc(X1,sK0) != iProver_top
% 3.14/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_2134]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2166,plain,
% 3.14/0.99      ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.14/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.14/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2161,c_2135]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1480,plain,
% 3.14/0.99      ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.14/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1471]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3023,plain,
% 3.14/0.99      ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_2166,c_26,c_44,c_1480]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3267,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.14/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK0)) = iProver_top
% 3.14/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.14/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_3023,c_968]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1397,plain,
% 3.14/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_1387,c_26,c_28,c_36]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6,plain,
% 3.14/0.99      ( v2_pre_topc(X0)
% 3.14/0.99      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.14/0.99      | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_844,plain,
% 3.14/0.99      ( v2_pre_topc(X0) = iProver_top
% 3.14/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 3.14/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1402,plain,
% 3.14/0.99      ( v2_pre_topc(sK1) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1397,c_844]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3269,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.14/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK0)) = iProver_top
% 3.14/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2161,c_968]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_11497,plain,
% 3.14/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.14/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK0)) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_3267,c_27,c_1402,c_3269]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_0,plain,
% 3.14/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.14/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_849,plain,
% 3.14/0.99      ( X0 = X1
% 3.14/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.14/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_11503,plain,
% 3.14/0.99      ( u1_struct_0(X0) = u1_struct_0(sK0)
% 3.14/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.14/0.99      | r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_11497,c_849]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_12351,plain,
% 3.14/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK0)
% 3.14/0.99      | m1_pre_topc(sK0,sK1) != iProver_top
% 3.14/0.99      | m1_pre_topc(sK1,sK0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_12340,c_11503]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_468,plain,
% 3.14/0.99      ( X0 != X1 | X2 != X3 | k2_tarski(X0,X2) = k2_tarski(X1,X3) ),
% 3.14/0.99      theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1840,plain,
% 3.14/0.99      ( X0 != u1_struct_0(sK0)
% 3.14/0.99      | X1 != k1_xboole_0
% 3.14/0.99      | k2_tarski(X1,X0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_468]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2898,plain,
% 3.14/0.99      ( X0 != u1_struct_0(sK0)
% 3.14/0.99      | k2_tarski(k1_xboole_0,X0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
% 3.14/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1840]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4185,plain,
% 3.14/0.99      ( k2_tarski(k1_xboole_0,u1_struct_0(X0)) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
% 3.14/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 3.14/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2898]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_9375,plain,
% 3.14/0.99      ( k2_tarski(k1_xboole_0,u1_struct_0(sK1)) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
% 3.14/0.99      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 3.14/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_4185]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.14/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 3.14/0.99      | ~ m1_pre_topc(X1,X2)
% 3.14/0.99      | ~ l1_pre_topc(X2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1047,plain,
% 3.14/0.99      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.14/0.99      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.14/0.99      | ~ m1_pre_topc(X0,X1)
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_8429,plain,
% 3.14/0.99      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | ~ m1_pre_topc(sK1,X0)
% 3.14/0.99      | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1047]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_8431,plain,
% 3.14/0.99      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.14/0.99      | ~ l1_pre_topc(sK0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_8429]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_11,plain,
% 3.14/0.99      ( ~ v1_tops_2(X0,X1)
% 3.14/0.99      | v1_tops_2(X0,X2)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.14/0.99      | ~ m1_pre_topc(X2,X1)
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1107,plain,
% 3.14/0.99      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 3.14/0.99      | v1_tops_2(u1_pre_topc(X0),X1)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.14/0.99      | ~ m1_pre_topc(X1,X0)
% 3.14/0.99      | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6330,plain,
% 3.14/0.99      ( v1_tops_2(u1_pre_topc(sK1),X0)
% 3.14/0.99      | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | ~ m1_pre_topc(X0,sK1)
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1107]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6332,plain,
% 3.14/0.99      ( v1_tops_2(u1_pre_topc(sK1),sK0)
% 3.14/0.99      | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | ~ m1_pre_topc(sK0,sK1)
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_6330]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4,plain,
% 3.14/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.14/0.99      | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4168,plain,
% 3.14/0.99      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_13,plain,
% 3.14/0.99      ( ~ v1_tops_2(X0,X1)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.14/0.99      | r1_tarski(X0,u1_pre_topc(X1))
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1360,plain,
% 3.14/0.99      ( ~ v1_tops_2(u1_pre_topc(X0),X1)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.14/0.99      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3848,plain,
% 3.14/0.99      ( ~ v1_tops_2(u1_pre_topc(sK1),X0)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.14/0.99      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0))
% 3.14/0.99      | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1360]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3850,plain,
% 3.14/0.99      ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.14/0.99      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
% 3.14/0.99      | ~ l1_pre_topc(sK0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_3848]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3453,plain,
% 3.14/0.99      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.14/0.99      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | ~ m1_pre_topc(X0,sK1)
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1047]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3455,plain,
% 3.14/0.99      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.14/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | ~ m1_pre_topc(sK0,sK1)
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_3453]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_12,plain,
% 3.14/0.99      ( v1_tops_2(X0,X1)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.14/0.99      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1595,plain,
% 3.14/0.99      ( v1_tops_2(u1_pre_topc(X0),X1)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.14/0.99      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2260,plain,
% 3.14/0.99      ( v1_tops_2(u1_pre_topc(X0),sK1)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1595]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3183,plain,
% 3.14/0.99      ( v1_tops_2(u1_pre_topc(sK1),sK1)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2260]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_457,plain,( X0 = X0 ),theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2899,plain,
% 3.14/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_457]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1974,plain,
% 3.14/0.99      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 3.14/0.99      | v1_tops_2(u1_pre_topc(X0),sK1)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | ~ m1_pre_topc(sK1,X0)
% 3.14/0.99      | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1107]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1976,plain,
% 3.14/0.99      ( ~ v1_tops_2(u1_pre_topc(sK0),sK0)
% 3.14/0.99      | v1_tops_2(u1_pre_topc(sK0),sK1)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.14/0.99      | ~ l1_pre_topc(sK0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1974]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1970,plain,
% 3.14/0.99      ( m1_pre_topc(sK1,sK0) | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1969]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_458,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1043,plain,
% 3.14/0.99      ( k2_tarski(k1_xboole_0,u1_struct_0(sK1)) != X0
% 3.14/0.99      | k2_tarski(k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK1)
% 3.14/0.99      | u1_pre_topc(sK1) != X0 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_458]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1762,plain,
% 3.14/0.99      ( k2_tarski(k1_xboole_0,u1_struct_0(sK1)) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
% 3.14/0.99      | k2_tarski(k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK1)
% 3.14/0.99      | u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1043]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1121,plain,
% 3.14/0.99      ( X0 != X1 | u1_pre_topc(X2) != X1 | u1_pre_topc(X2) = X0 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_458]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1290,plain,
% 3.14/0.99      ( X0 != u1_pre_topc(X1)
% 3.14/0.99      | u1_pre_topc(X2) = X0
% 3.14/0.99      | u1_pre_topc(X2) != u1_pre_topc(X1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1121]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1516,plain,
% 3.14/0.99      ( k2_tarski(k1_xboole_0,u1_struct_0(sK0)) != u1_pre_topc(sK0)
% 3.14/0.99      | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
% 3.14/0.99      | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1290]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1761,plain,
% 3.14/0.99      ( k2_tarski(k1_xboole_0,u1_struct_0(sK0)) != u1_pre_topc(sK0)
% 3.14/0.99      | u1_pre_topc(sK1) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
% 3.14/0.99      | u1_pre_topc(sK1) != u1_pre_topc(sK0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1516]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1701,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.14/0.99      | m1_pre_topc(X0,sK1)
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1678]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1703,plain,
% 3.14/0.99      ( ~ m1_pre_topc(sK0,sK0)
% 3.14/0.99      | m1_pre_topc(sK0,sK1)
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1701]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1078,plain,
% 3.14/0.99      ( ~ r1_tarski(X0,u1_pre_topc(sK1))
% 3.14/0.99      | ~ r1_tarski(u1_pre_topc(sK1),X0)
% 3.14/0.99      | u1_pre_topc(sK1) = X0 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1607,plain,
% 3.14/0.99      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
% 3.14/0.99      | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0))
% 3.14/0.99      | u1_pre_topc(sK1) = u1_pre_topc(X0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1078]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1613,plain,
% 3.14/0.99      ( ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
% 3.14/0.99      | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
% 3.14/0.99      | u1_pre_topc(sK1) = u1_pre_topc(sK0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1607]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1606,plain,
% 3.14/0.99      ( ~ v1_tops_2(u1_pre_topc(X0),sK1)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1360]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1609,plain,
% 3.14/0.99      ( ~ v1_tops_2(u1_pre_topc(sK0),sK1)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.14/0.99      | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1606]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2,plain,
% 3.14/0.99      ( r1_tarski(X0,X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1050,plain,
% 3.14/0.99      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1177,plain,
% 3.14/0.99      ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1050]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1051,plain,
% 3.14/0.99      ( v1_tops_2(u1_pre_topc(X0),X0)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.14/0.99      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
% 3.14/0.99      | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1057,plain,
% 3.14/0.99      ( v1_tops_2(u1_pre_topc(sK0),sK0)
% 3.14/0.99      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.14/0.99      | ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0))
% 3.14/0.99      | ~ l1_pre_topc(sK0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1051]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1053,plain,
% 3.14/0.99      ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1050]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_19,plain,
% 3.14/0.99      ( v2_tdlat_3(X0)
% 3.14/0.99      | ~ l1_pre_topc(X0)
% 3.14/0.99      | k2_tarski(k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_21,negated_conjecture,
% 3.14/0.99      ( ~ v2_tdlat_3(sK1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_281,plain,
% 3.14/0.99      ( ~ l1_pre_topc(X0)
% 3.14/0.99      | k2_tarski(k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0)
% 3.14/0.99      | sK1 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_282,plain,
% 3.14/0.99      ( ~ l1_pre_topc(sK1)
% 3.14/0.99      | k2_tarski(k1_xboole_0,u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_281]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_65,plain,
% 3.14/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.14/0.99      | ~ l1_pre_topc(sK0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_43,plain,
% 3.14/0.99      ( m1_pre_topc(sK0,sK0) | ~ l1_pre_topc(sK0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_20,plain,
% 3.14/0.99      ( ~ v2_tdlat_3(X0)
% 3.14/0.99      | ~ l1_pre_topc(X0)
% 3.14/0.99      | k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_31,plain,
% 3.14/0.99      ( ~ v2_tdlat_3(sK0)
% 3.14/0.99      | ~ l1_pre_topc(sK0)
% 3.14/0.99      | k2_tarski(k1_xboole_0,u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(contradiction,plain,
% 3.14/0.99      ( $false ),
% 3.14/0.99      inference(minisat,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_12351,c_9375,c_8431,c_6332,c_4168,c_3850,c_3455,
% 3.14/0.99                 c_3183,c_2899,c_1976,c_1970,c_1969,c_1762,c_1761,c_1703,
% 3.14/0.99                 c_1702,c_1613,c_1609,c_1177,c_1057,c_1053,c_282,c_65,
% 3.14/0.99                 c_44,c_43,c_31,c_22,c_27,c_24,c_26,c_25]) ).
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  ------                               Statistics
% 3.14/0.99  
% 3.14/0.99  ------ General
% 3.14/0.99  
% 3.14/0.99  abstr_ref_over_cycles:                  0
% 3.14/0.99  abstr_ref_under_cycles:                 0
% 3.14/0.99  gc_basic_clause_elim:                   0
% 3.14/0.99  forced_gc_time:                         0
% 3.14/0.99  parsing_time:                           0.011
% 3.14/0.99  unif_index_cands_time:                  0.
% 3.14/0.99  unif_index_add_time:                    0.
% 3.14/0.99  orderings_time:                         0.
% 3.14/0.99  out_proof_time:                         0.012
% 3.14/0.99  total_time:                             0.323
% 3.14/0.99  num_of_symbols:                         46
% 3.14/0.99  num_of_terms:                           3014
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing
% 3.14/0.99  
% 3.14/0.99  num_of_splits:                          0
% 3.14/0.99  num_of_split_atoms:                     0
% 3.14/0.99  num_of_reused_defs:                     0
% 3.14/0.99  num_eq_ax_congr_red:                    9
% 3.14/0.99  num_of_sem_filtered_clauses:            1
% 3.14/0.99  num_of_subtypes:                        0
% 3.14/0.99  monotx_restored_types:                  0
% 3.14/0.99  sat_num_of_epr_types:                   0
% 3.14/0.99  sat_num_of_non_cyclic_types:            0
% 3.14/0.99  sat_guarded_non_collapsed_types:        0
% 3.14/0.99  num_pure_diseq_elim:                    0
% 3.14/0.99  simp_replaced_by:                       0
% 3.14/0.99  res_preprocessed:                       121
% 3.14/0.99  prep_upred:                             0
% 3.14/0.99  prep_unflattend:                        3
% 3.14/0.99  smt_new_axioms:                         0
% 3.14/0.99  pred_elim_cands:                        6
% 3.14/0.99  pred_elim:                              1
% 3.14/0.99  pred_elim_cl:                           0
% 3.14/0.99  pred_elim_cycles:                       3
% 3.14/0.99  merged_defs:                            0
% 3.14/0.99  merged_defs_ncl:                        0
% 3.14/0.99  bin_hyper_res:                          0
% 3.14/0.99  prep_cycles:                            4
% 3.14/0.99  pred_elim_time:                         0.001
% 3.14/0.99  splitting_time:                         0.
% 3.14/0.99  sem_filter_time:                        0.
% 3.14/0.99  monotx_time:                            0.
% 3.14/0.99  subtype_inf_time:                       0.
% 3.14/0.99  
% 3.14/0.99  ------ Problem properties
% 3.14/0.99  
% 3.14/0.99  clauses:                                24
% 3.14/0.99  conjectures:                            3
% 3.14/0.99  epr:                                    9
% 3.14/0.99  horn:                                   24
% 3.14/0.99  ground:                                 7
% 3.14/0.99  unary:                                  8
% 3.14/0.99  binary:                                 2
% 3.14/0.99  lits:                                   68
% 3.14/0.99  lits_eq:                                6
% 3.14/0.99  fd_pure:                                0
% 3.14/0.99  fd_pseudo:                              0
% 3.14/0.99  fd_cond:                                0
% 3.14/0.99  fd_pseudo_cond:                         1
% 3.14/0.99  ac_symbols:                             0
% 3.14/0.99  
% 3.14/0.99  ------ Propositional Solver
% 3.14/0.99  
% 3.14/0.99  prop_solver_calls:                      31
% 3.14/0.99  prop_fast_solver_calls:                 1554
% 3.14/0.99  smt_solver_calls:                       0
% 3.14/0.99  smt_fast_solver_calls:                  0
% 3.14/0.99  prop_num_of_clauses:                    2256
% 3.14/0.99  prop_preprocess_simplified:             6897
% 3.14/0.99  prop_fo_subsumed:                       98
% 3.14/0.99  prop_solver_time:                       0.
% 3.14/0.99  smt_solver_time:                        0.
% 3.14/0.99  smt_fast_solver_time:                   0.
% 3.14/0.99  prop_fast_solver_time:                  0.
% 3.14/0.99  prop_unsat_core_time:                   0.
% 3.14/0.99  
% 3.14/0.99  ------ QBF
% 3.14/0.99  
% 3.14/0.99  qbf_q_res:                              0
% 3.14/0.99  qbf_num_tautologies:                    0
% 3.14/0.99  qbf_prep_cycles:                        0
% 3.14/0.99  
% 3.14/0.99  ------ BMC1
% 3.14/0.99  
% 3.14/0.99  bmc1_current_bound:                     -1
% 3.14/0.99  bmc1_last_solved_bound:                 -1
% 3.14/0.99  bmc1_unsat_core_size:                   -1
% 3.14/0.99  bmc1_unsat_core_parents_size:           -1
% 3.14/0.99  bmc1_merge_next_fun:                    0
% 3.14/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.14/0.99  
% 3.14/0.99  ------ Instantiation
% 3.14/0.99  
% 3.14/0.99  inst_num_of_clauses:                    633
% 3.14/0.99  inst_num_in_passive:                    113
% 3.14/0.99  inst_num_in_active:                     507
% 3.14/0.99  inst_num_in_unprocessed:                13
% 3.14/0.99  inst_num_of_loops:                      590
% 3.14/0.99  inst_num_of_learning_restarts:          0
% 3.14/0.99  inst_num_moves_active_passive:          75
% 3.14/0.99  inst_lit_activity:                      0
% 3.14/0.99  inst_lit_activity_moves:                0
% 3.14/0.99  inst_num_tautologies:                   0
% 3.14/0.99  inst_num_prop_implied:                  0
% 3.14/0.99  inst_num_existing_simplified:           0
% 3.14/0.99  inst_num_eq_res_simplified:             0
% 3.14/0.99  inst_num_child_elim:                    0
% 3.14/0.99  inst_num_of_dismatching_blockings:      846
% 3.14/0.99  inst_num_of_non_proper_insts:           1888
% 3.14/0.99  inst_num_of_duplicates:                 0
% 3.14/0.99  inst_inst_num_from_inst_to_res:         0
% 3.14/0.99  inst_dismatching_checking_time:         0.
% 3.14/0.99  
% 3.14/0.99  ------ Resolution
% 3.14/0.99  
% 3.14/0.99  res_num_of_clauses:                     0
% 3.14/0.99  res_num_in_passive:                     0
% 3.14/0.99  res_num_in_active:                      0
% 3.14/0.99  res_num_of_loops:                       125
% 3.14/0.99  res_forward_subset_subsumed:            307
% 3.14/0.99  res_backward_subset_subsumed:           2
% 3.14/0.99  res_forward_subsumed:                   0
% 3.14/0.99  res_backward_subsumed:                  0
% 3.14/0.99  res_forward_subsumption_resolution:     0
% 3.14/0.99  res_backward_subsumption_resolution:    0
% 3.14/0.99  res_clause_to_clause_subsumption:       2985
% 3.14/0.99  res_orphan_elimination:                 0
% 3.14/0.99  res_tautology_del:                      198
% 3.14/0.99  res_num_eq_res_simplified:              0
% 3.14/0.99  res_num_sel_changes:                    0
% 3.14/0.99  res_moves_from_active_to_pass:          0
% 3.14/0.99  
% 3.14/0.99  ------ Superposition
% 3.14/0.99  
% 3.14/0.99  sup_time_total:                         0.
% 3.14/0.99  sup_time_generating:                    0.
% 3.14/0.99  sup_time_sim_full:                      0.
% 3.14/0.99  sup_time_sim_immed:                     0.
% 3.14/0.99  
% 3.14/0.99  sup_num_of_clauses:                     264
% 3.14/0.99  sup_num_in_active:                      117
% 3.14/0.99  sup_num_in_passive:                     147
% 3.14/0.99  sup_num_of_loops:                       116
% 3.14/0.99  sup_fw_superposition:                   284
% 3.14/0.99  sup_bw_superposition:                   305
% 3.14/0.99  sup_immediate_simplified:               218
% 3.14/0.99  sup_given_eliminated:                   0
% 3.14/0.99  comparisons_done:                       0
% 3.14/0.99  comparisons_avoided:                    0
% 3.14/0.99  
% 3.14/0.99  ------ Simplifications
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  sim_fw_subset_subsumed:                 77
% 3.14/0.99  sim_bw_subset_subsumed:                 9
% 3.14/0.99  sim_fw_subsumed:                        123
% 3.14/0.99  sim_bw_subsumed:                        5
% 3.14/0.99  sim_fw_subsumption_res:                 7
% 3.14/0.99  sim_bw_subsumption_res:                 0
% 3.14/0.99  sim_tautology_del:                      51
% 3.14/0.99  sim_eq_tautology_del:                   7
% 3.14/0.99  sim_eq_res_simp:                        0
% 3.14/0.99  sim_fw_demodulated:                     0
% 3.14/0.99  sim_bw_demodulated:                     0
% 3.14/0.99  sim_light_normalised:                   24
% 3.14/0.99  sim_joinable_taut:                      0
% 3.14/0.99  sim_joinable_simp:                      0
% 3.14/0.99  sim_ac_normalised:                      0
% 3.14/0.99  sim_smt_subsumption:                    0
% 3.14/0.99  
%------------------------------------------------------------------------------
