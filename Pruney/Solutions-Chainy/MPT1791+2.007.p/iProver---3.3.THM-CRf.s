%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:50 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  167 (2882 expanded)
%              Number of clauses        :  110 ( 775 expanded)
%              Number of leaves         :   13 ( 627 expanded)
%              Depth                    :   24
%              Number of atoms          :  553 (15458 expanded)
%              Number of equality atoms :  159 (3794 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1)
          | ~ v3_pre_topc(sK1,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1)
          | v3_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f65,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_177,plain,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_177])).

cnf(c_409,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_411,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_20,c_19])).

cnf(c_931,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_20,c_19,c_409])).

cnf(c_1180,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_931])).

cnf(c_1613,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | r2_hidden(sK1,u1_pre_topc(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1180])).

cnf(c_1182,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1611,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1182])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X0,u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X0,u1_pre_topc(sK0))
    | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_21,c_20])).

cnf(c_1177,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X0_47,u1_pre_topc(sK0))
    | k5_tmap_1(sK0,X0_47) = u1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_500])).

cnf(c_1616,plain,
    ( k5_tmap_1(sK0,X0_47) = u1_pre_topc(sK0)
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(X0_47,u1_pre_topc(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1177])).

cnf(c_2004,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1611,c_1616])).

cnf(c_2054,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1613,c_2004])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_306,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_5,c_4])).

cnf(c_723,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_306,c_20])).

cnf(c_724,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_1169,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_724])).

cnf(c_1622,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1169])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_317,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_5,c_1])).

cnf(c_718,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_20])).

cnf(c_719,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_1170,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_719])).

cnf(c_1633,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1622,c_1170])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_21,c_20])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK0,X0) != X1
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_542])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,X0))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_615,c_21,c_20,c_574])).

cnf(c_1175,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0_47)),u1_pre_topc(k6_tmap_1(sK0,X0_47))) = k6_tmap_1(sK0,X0_47) ),
    inference(subtyping,[status(esa)],[c_619])).

cnf(c_1618,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0_47)),u1_pre_topc(k6_tmap_1(sK0,X0_47))) = k6_tmap_1(sK0,X0_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_2320,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1633,c_1618])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_21,c_20])).

cnf(c_1179,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k6_tmap_1(sK0,X0_47)) = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_464])).

cnf(c_1614,plain,
    ( u1_struct_0(k6_tmap_1(sK0,X0_47)) = u1_struct_0(sK0)
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1179])).

cnf(c_1750,plain,
    ( u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1633,c_1614])).

cnf(c_2322,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_2320,c_1750])).

cnf(c_2005,plain,
    ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(sK0)
    | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1616])).

cnf(c_7,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_635,plain,
    ( ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_636,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_55,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_638,plain,
    ( k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_636,c_21,c_20,c_55])).

cnf(c_1174,plain,
    ( k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_638])).

cnf(c_1630,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1174,c_1170])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(k1_tops_1(X1,X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | k1_tops_1(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k1_tops_1(X1,X0),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k1_tops_1(X1,X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_374,c_21])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_666,plain,
    ( r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_20])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0)) ),
    inference(renaming,[status(thm)],[c_666])).

cnf(c_1172,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0_47),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k1_tops_1(sK0,X0_47),u1_pre_topc(sK0)) ),
    inference(subtyping,[status(esa)],[c_667])).

cnf(c_1620,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_47),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(k1_tops_1(sK0,X0_47),u1_pre_topc(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1172])).

cnf(c_2161,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(k1_tops_1(sK0,u1_struct_0(sK0)),u1_pre_topc(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1630,c_1620])).

cnf(c_2162,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2161,c_1630])).

cnf(c_2246,plain,
    ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2005,c_1633,c_2162])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_21,c_20])).

cnf(c_1178,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,X0_47)) = k5_tmap_1(sK0,X0_47) ),
    inference(subtyping,[status(esa)],[c_482])).

cnf(c_1615,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,X0_47)) = k5_tmap_1(sK0,X0_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1178])).

cnf(c_1828,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) = k5_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1633,c_1615])).

cnf(c_2249,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) = u1_pre_topc(sK0) ),
    inference(demodulation,[status(thm)],[c_2246,c_1828])).

cnf(c_2915,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_2322,c_2249])).

cnf(c_2929,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | k6_tmap_1(sK0,u1_struct_0(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2054,c_2915])).

cnf(c_3076,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | u1_pre_topc(k6_tmap_1(sK0,sK1)) = u1_pre_topc(sK0) ),
    inference(superposition,[status(thm)],[c_2929,c_2249])).

cnf(c_1827,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1611,c_1615])).

cnf(c_3080,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(demodulation,[status(thm)],[c_3076,c_1827])).

cnf(c_2319,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1611,c_1618])).

cnf(c_1749,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1611,c_1614])).

cnf(c_2325,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2319,c_1749,c_1827])).

cnf(c_3143,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3080,c_2325])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X0,u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X0,u1_pre_topc(sK0))
    | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_21,c_20])).

cnf(c_1176,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X0_47,u1_pre_topc(sK0))
    | k5_tmap_1(sK0,X0_47) != u1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_521])).

cnf(c_1229,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_175,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_175])).

cnf(c_395,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_397,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_20,c_19])).

cnf(c_929,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_20,c_19,c_395])).

cnf(c_1181,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_929])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3143,c_3080,c_1229,c_1181,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:34:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.53/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/0.99  
% 2.53/0.99  ------  iProver source info
% 2.53/0.99  
% 2.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/0.99  git: non_committed_changes: false
% 2.53/0.99  git: last_make_outside_of_git: false
% 2.53/0.99  
% 2.53/0.99  ------ 
% 2.53/0.99  
% 2.53/0.99  ------ Input Options
% 2.53/0.99  
% 2.53/0.99  --out_options                           all
% 2.53/0.99  --tptp_safe_out                         true
% 2.53/0.99  --problem_path                          ""
% 2.53/0.99  --include_path                          ""
% 2.53/0.99  --clausifier                            res/vclausify_rel
% 2.53/0.99  --clausifier_options                    --mode clausify
% 2.53/0.99  --stdin                                 false
% 2.53/0.99  --stats_out                             all
% 2.53/0.99  
% 2.53/0.99  ------ General Options
% 2.53/0.99  
% 2.53/0.99  --fof                                   false
% 2.53/0.99  --time_out_real                         305.
% 2.53/0.99  --time_out_virtual                      -1.
% 2.53/0.99  --symbol_type_check                     false
% 2.53/0.99  --clausify_out                          false
% 2.53/0.99  --sig_cnt_out                           false
% 2.53/0.99  --trig_cnt_out                          false
% 2.53/0.99  --trig_cnt_out_tolerance                1.
% 2.53/0.99  --trig_cnt_out_sk_spl                   false
% 2.53/0.99  --abstr_cl_out                          false
% 2.53/0.99  
% 2.53/0.99  ------ Global Options
% 2.53/0.99  
% 2.53/0.99  --schedule                              default
% 2.53/0.99  --add_important_lit                     false
% 2.53/0.99  --prop_solver_per_cl                    1000
% 2.53/0.99  --min_unsat_core                        false
% 2.53/0.99  --soft_assumptions                      false
% 2.53/0.99  --soft_lemma_size                       3
% 2.53/0.99  --prop_impl_unit_size                   0
% 2.53/0.99  --prop_impl_unit                        []
% 2.53/0.99  --share_sel_clauses                     true
% 2.53/0.99  --reset_solvers                         false
% 2.53/0.99  --bc_imp_inh                            [conj_cone]
% 2.53/0.99  --conj_cone_tolerance                   3.
% 2.53/0.99  --extra_neg_conj                        none
% 2.53/0.99  --large_theory_mode                     true
% 2.53/0.99  --prolific_symb_bound                   200
% 2.53/0.99  --lt_threshold                          2000
% 2.53/0.99  --clause_weak_htbl                      true
% 2.53/0.99  --gc_record_bc_elim                     false
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing Options
% 2.53/0.99  
% 2.53/0.99  --preprocessing_flag                    true
% 2.53/0.99  --time_out_prep_mult                    0.1
% 2.53/0.99  --splitting_mode                        input
% 2.53/0.99  --splitting_grd                         true
% 2.53/0.99  --splitting_cvd                         false
% 2.53/0.99  --splitting_cvd_svl                     false
% 2.53/0.99  --splitting_nvd                         32
% 2.53/0.99  --sub_typing                            true
% 2.53/0.99  --prep_gs_sim                           true
% 2.53/0.99  --prep_unflatten                        true
% 2.53/0.99  --prep_res_sim                          true
% 2.53/0.99  --prep_upred                            true
% 2.53/0.99  --prep_sem_filter                       exhaustive
% 2.53/0.99  --prep_sem_filter_out                   false
% 2.53/0.99  --pred_elim                             true
% 2.53/0.99  --res_sim_input                         true
% 2.53/0.99  --eq_ax_congr_red                       true
% 2.53/0.99  --pure_diseq_elim                       true
% 2.53/0.99  --brand_transform                       false
% 2.53/0.99  --non_eq_to_eq                          false
% 2.53/0.99  --prep_def_merge                        true
% 2.53/0.99  --prep_def_merge_prop_impl              false
% 2.53/0.99  --prep_def_merge_mbd                    true
% 2.53/0.99  --prep_def_merge_tr_red                 false
% 2.53/0.99  --prep_def_merge_tr_cl                  false
% 2.53/0.99  --smt_preprocessing                     true
% 2.53/0.99  --smt_ac_axioms                         fast
% 2.53/0.99  --preprocessed_out                      false
% 2.53/0.99  --preprocessed_stats                    false
% 2.53/0.99  
% 2.53/0.99  ------ Abstraction refinement Options
% 2.53/0.99  
% 2.53/0.99  --abstr_ref                             []
% 2.53/0.99  --abstr_ref_prep                        false
% 2.53/0.99  --abstr_ref_until_sat                   false
% 2.53/0.99  --abstr_ref_sig_restrict                funpre
% 2.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/0.99  --abstr_ref_under                       []
% 2.53/0.99  
% 2.53/0.99  ------ SAT Options
% 2.53/0.99  
% 2.53/0.99  --sat_mode                              false
% 2.53/0.99  --sat_fm_restart_options                ""
% 2.53/0.99  --sat_gr_def                            false
% 2.53/0.99  --sat_epr_types                         true
% 2.53/0.99  --sat_non_cyclic_types                  false
% 2.53/0.99  --sat_finite_models                     false
% 2.53/0.99  --sat_fm_lemmas                         false
% 2.53/0.99  --sat_fm_prep                           false
% 2.53/0.99  --sat_fm_uc_incr                        true
% 2.53/0.99  --sat_out_model                         small
% 2.53/0.99  --sat_out_clauses                       false
% 2.53/0.99  
% 2.53/0.99  ------ QBF Options
% 2.53/0.99  
% 2.53/0.99  --qbf_mode                              false
% 2.53/0.99  --qbf_elim_univ                         false
% 2.53/0.99  --qbf_dom_inst                          none
% 2.53/0.99  --qbf_dom_pre_inst                      false
% 2.53/0.99  --qbf_sk_in                             false
% 2.53/0.99  --qbf_pred_elim                         true
% 2.53/0.99  --qbf_split                             512
% 2.53/0.99  
% 2.53/0.99  ------ BMC1 Options
% 2.53/0.99  
% 2.53/0.99  --bmc1_incremental                      false
% 2.53/0.99  --bmc1_axioms                           reachable_all
% 2.53/0.99  --bmc1_min_bound                        0
% 2.53/0.99  --bmc1_max_bound                        -1
% 2.53/0.99  --bmc1_max_bound_default                -1
% 2.53/0.99  --bmc1_symbol_reachability              true
% 2.53/0.99  --bmc1_property_lemmas                  false
% 2.53/0.99  --bmc1_k_induction                      false
% 2.53/0.99  --bmc1_non_equiv_states                 false
% 2.53/0.99  --bmc1_deadlock                         false
% 2.53/0.99  --bmc1_ucm                              false
% 2.53/0.99  --bmc1_add_unsat_core                   none
% 2.53/0.99  --bmc1_unsat_core_children              false
% 2.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/0.99  --bmc1_out_stat                         full
% 2.53/0.99  --bmc1_ground_init                      false
% 2.53/0.99  --bmc1_pre_inst_next_state              false
% 2.53/0.99  --bmc1_pre_inst_state                   false
% 2.53/0.99  --bmc1_pre_inst_reach_state             false
% 2.53/0.99  --bmc1_out_unsat_core                   false
% 2.53/0.99  --bmc1_aig_witness_out                  false
% 2.53/0.99  --bmc1_verbose                          false
% 2.53/0.99  --bmc1_dump_clauses_tptp                false
% 2.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.53/0.99  --bmc1_dump_file                        -
% 2.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.53/0.99  --bmc1_ucm_extend_mode                  1
% 2.53/0.99  --bmc1_ucm_init_mode                    2
% 2.53/0.99  --bmc1_ucm_cone_mode                    none
% 2.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.53/0.99  --bmc1_ucm_relax_model                  4
% 2.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/0.99  --bmc1_ucm_layered_model                none
% 2.53/0.99  --bmc1_ucm_max_lemma_size               10
% 2.53/0.99  
% 2.53/0.99  ------ AIG Options
% 2.53/0.99  
% 2.53/0.99  --aig_mode                              false
% 2.53/0.99  
% 2.53/0.99  ------ Instantiation Options
% 2.53/0.99  
% 2.53/0.99  --instantiation_flag                    true
% 2.53/0.99  --inst_sos_flag                         false
% 2.53/0.99  --inst_sos_phase                        true
% 2.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel_side                     num_symb
% 2.53/0.99  --inst_solver_per_active                1400
% 2.53/0.99  --inst_solver_calls_frac                1.
% 2.53/0.99  --inst_passive_queue_type               priority_queues
% 2.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/0.99  --inst_passive_queues_freq              [25;2]
% 2.53/0.99  --inst_dismatching                      true
% 2.53/0.99  --inst_eager_unprocessed_to_passive     true
% 2.53/0.99  --inst_prop_sim_given                   true
% 2.53/0.99  --inst_prop_sim_new                     false
% 2.53/0.99  --inst_subs_new                         false
% 2.53/0.99  --inst_eq_res_simp                      false
% 2.53/0.99  --inst_subs_given                       false
% 2.53/0.99  --inst_orphan_elimination               true
% 2.53/0.99  --inst_learning_loop_flag               true
% 2.53/0.99  --inst_learning_start                   3000
% 2.53/0.99  --inst_learning_factor                  2
% 2.53/0.99  --inst_start_prop_sim_after_learn       3
% 2.53/0.99  --inst_sel_renew                        solver
% 2.53/0.99  --inst_lit_activity_flag                true
% 2.53/0.99  --inst_restr_to_given                   false
% 2.53/0.99  --inst_activity_threshold               500
% 2.53/0.99  --inst_out_proof                        true
% 2.53/0.99  
% 2.53/0.99  ------ Resolution Options
% 2.53/0.99  
% 2.53/0.99  --resolution_flag                       true
% 2.53/0.99  --res_lit_sel                           adaptive
% 2.53/0.99  --res_lit_sel_side                      none
% 2.53/0.99  --res_ordering                          kbo
% 2.53/0.99  --res_to_prop_solver                    active
% 2.53/0.99  --res_prop_simpl_new                    false
% 2.53/0.99  --res_prop_simpl_given                  true
% 2.53/0.99  --res_passive_queue_type                priority_queues
% 2.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/0.99  --res_passive_queues_freq               [15;5]
% 2.53/0.99  --res_forward_subs                      full
% 2.53/0.99  --res_backward_subs                     full
% 2.53/0.99  --res_forward_subs_resolution           true
% 2.53/0.99  --res_backward_subs_resolution          true
% 2.53/0.99  --res_orphan_elimination                true
% 2.53/0.99  --res_time_limit                        2.
% 2.53/0.99  --res_out_proof                         true
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Options
% 2.53/0.99  
% 2.53/0.99  --superposition_flag                    true
% 2.53/0.99  --sup_passive_queue_type                priority_queues
% 2.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.53/0.99  --demod_completeness_check              fast
% 2.53/0.99  --demod_use_ground                      true
% 2.53/0.99  --sup_to_prop_solver                    passive
% 2.53/0.99  --sup_prop_simpl_new                    true
% 2.53/0.99  --sup_prop_simpl_given                  true
% 2.53/0.99  --sup_fun_splitting                     false
% 2.53/0.99  --sup_smt_interval                      50000
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Simplification Setup
% 2.53/0.99  
% 2.53/0.99  --sup_indices_passive                   []
% 2.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_full_bw                           [BwDemod]
% 2.53/0.99  --sup_immed_triv                        [TrivRules]
% 2.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_immed_bw_main                     []
% 2.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  
% 2.53/0.99  ------ Combination Options
% 2.53/0.99  
% 2.53/0.99  --comb_res_mult                         3
% 2.53/0.99  --comb_sup_mult                         2
% 2.53/0.99  --comb_inst_mult                        10
% 2.53/0.99  
% 2.53/0.99  ------ Debug Options
% 2.53/0.99  
% 2.53/0.99  --dbg_backtrace                         false
% 2.53/0.99  --dbg_dump_prop_clauses                 false
% 2.53/0.99  --dbg_dump_prop_clauses_file            -
% 2.53/0.99  --dbg_out_stat                          false
% 2.53/0.99  ------ Parsing...
% 2.53/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/0.99  ------ Proving...
% 2.53/0.99  ------ Problem Properties 
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  clauses                                 17
% 2.53/0.99  conjectures                             1
% 2.53/0.99  EPR                                     0
% 2.53/0.99  Horn                                    16
% 2.53/0.99  unary                                   4
% 2.53/0.99  binary                                  8
% 2.53/0.99  lits                                    36
% 2.53/0.99  lits eq                                 12
% 2.53/0.99  fd_pure                                 0
% 2.53/0.99  fd_pseudo                               0
% 2.53/0.99  fd_cond                                 0
% 2.53/0.99  fd_pseudo_cond                          0
% 2.53/0.99  AC symbols                              0
% 2.53/0.99  
% 2.53/0.99  ------ Schedule dynamic 5 is on 
% 2.53/0.99  
% 2.53/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  ------ 
% 2.53/0.99  Current options:
% 2.53/0.99  ------ 
% 2.53/0.99  
% 2.53/0.99  ------ Input Options
% 2.53/0.99  
% 2.53/0.99  --out_options                           all
% 2.53/0.99  --tptp_safe_out                         true
% 2.53/0.99  --problem_path                          ""
% 2.53/0.99  --include_path                          ""
% 2.53/0.99  --clausifier                            res/vclausify_rel
% 2.53/0.99  --clausifier_options                    --mode clausify
% 2.53/0.99  --stdin                                 false
% 2.53/0.99  --stats_out                             all
% 2.53/0.99  
% 2.53/0.99  ------ General Options
% 2.53/0.99  
% 2.53/0.99  --fof                                   false
% 2.53/0.99  --time_out_real                         305.
% 2.53/0.99  --time_out_virtual                      -1.
% 2.53/0.99  --symbol_type_check                     false
% 2.53/0.99  --clausify_out                          false
% 2.53/0.99  --sig_cnt_out                           false
% 2.53/0.99  --trig_cnt_out                          false
% 2.53/0.99  --trig_cnt_out_tolerance                1.
% 2.53/0.99  --trig_cnt_out_sk_spl                   false
% 2.53/0.99  --abstr_cl_out                          false
% 2.53/0.99  
% 2.53/0.99  ------ Global Options
% 2.53/0.99  
% 2.53/0.99  --schedule                              default
% 2.53/0.99  --add_important_lit                     false
% 2.53/0.99  --prop_solver_per_cl                    1000
% 2.53/0.99  --min_unsat_core                        false
% 2.53/0.99  --soft_assumptions                      false
% 2.53/0.99  --soft_lemma_size                       3
% 2.53/0.99  --prop_impl_unit_size                   0
% 2.53/0.99  --prop_impl_unit                        []
% 2.53/0.99  --share_sel_clauses                     true
% 2.53/0.99  --reset_solvers                         false
% 2.53/0.99  --bc_imp_inh                            [conj_cone]
% 2.53/0.99  --conj_cone_tolerance                   3.
% 2.53/0.99  --extra_neg_conj                        none
% 2.53/0.99  --large_theory_mode                     true
% 2.53/0.99  --prolific_symb_bound                   200
% 2.53/0.99  --lt_threshold                          2000
% 2.53/0.99  --clause_weak_htbl                      true
% 2.53/0.99  --gc_record_bc_elim                     false
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing Options
% 2.53/0.99  
% 2.53/0.99  --preprocessing_flag                    true
% 2.53/0.99  --time_out_prep_mult                    0.1
% 2.53/0.99  --splitting_mode                        input
% 2.53/0.99  --splitting_grd                         true
% 2.53/0.99  --splitting_cvd                         false
% 2.53/0.99  --splitting_cvd_svl                     false
% 2.53/0.99  --splitting_nvd                         32
% 2.53/0.99  --sub_typing                            true
% 2.53/0.99  --prep_gs_sim                           true
% 2.53/0.99  --prep_unflatten                        true
% 2.53/0.99  --prep_res_sim                          true
% 2.53/0.99  --prep_upred                            true
% 2.53/0.99  --prep_sem_filter                       exhaustive
% 2.53/0.99  --prep_sem_filter_out                   false
% 2.53/0.99  --pred_elim                             true
% 2.53/0.99  --res_sim_input                         true
% 2.53/0.99  --eq_ax_congr_red                       true
% 2.53/0.99  --pure_diseq_elim                       true
% 2.53/0.99  --brand_transform                       false
% 2.53/0.99  --non_eq_to_eq                          false
% 2.53/0.99  --prep_def_merge                        true
% 2.53/0.99  --prep_def_merge_prop_impl              false
% 2.53/0.99  --prep_def_merge_mbd                    true
% 2.53/0.99  --prep_def_merge_tr_red                 false
% 2.53/0.99  --prep_def_merge_tr_cl                  false
% 2.53/0.99  --smt_preprocessing                     true
% 2.53/0.99  --smt_ac_axioms                         fast
% 2.53/0.99  --preprocessed_out                      false
% 2.53/0.99  --preprocessed_stats                    false
% 2.53/0.99  
% 2.53/0.99  ------ Abstraction refinement Options
% 2.53/0.99  
% 2.53/0.99  --abstr_ref                             []
% 2.53/0.99  --abstr_ref_prep                        false
% 2.53/0.99  --abstr_ref_until_sat                   false
% 2.53/0.99  --abstr_ref_sig_restrict                funpre
% 2.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/0.99  --abstr_ref_under                       []
% 2.53/0.99  
% 2.53/0.99  ------ SAT Options
% 2.53/0.99  
% 2.53/0.99  --sat_mode                              false
% 2.53/0.99  --sat_fm_restart_options                ""
% 2.53/0.99  --sat_gr_def                            false
% 2.53/0.99  --sat_epr_types                         true
% 2.53/0.99  --sat_non_cyclic_types                  false
% 2.53/0.99  --sat_finite_models                     false
% 2.53/0.99  --sat_fm_lemmas                         false
% 2.53/0.99  --sat_fm_prep                           false
% 2.53/0.99  --sat_fm_uc_incr                        true
% 2.53/0.99  --sat_out_model                         small
% 2.53/0.99  --sat_out_clauses                       false
% 2.53/0.99  
% 2.53/0.99  ------ QBF Options
% 2.53/0.99  
% 2.53/0.99  --qbf_mode                              false
% 2.53/0.99  --qbf_elim_univ                         false
% 2.53/0.99  --qbf_dom_inst                          none
% 2.53/0.99  --qbf_dom_pre_inst                      false
% 2.53/0.99  --qbf_sk_in                             false
% 2.53/0.99  --qbf_pred_elim                         true
% 2.53/0.99  --qbf_split                             512
% 2.53/0.99  
% 2.53/0.99  ------ BMC1 Options
% 2.53/0.99  
% 2.53/0.99  --bmc1_incremental                      false
% 2.53/0.99  --bmc1_axioms                           reachable_all
% 2.53/0.99  --bmc1_min_bound                        0
% 2.53/0.99  --bmc1_max_bound                        -1
% 2.53/0.99  --bmc1_max_bound_default                -1
% 2.53/0.99  --bmc1_symbol_reachability              true
% 2.53/0.99  --bmc1_property_lemmas                  false
% 2.53/0.99  --bmc1_k_induction                      false
% 2.53/0.99  --bmc1_non_equiv_states                 false
% 2.53/0.99  --bmc1_deadlock                         false
% 2.53/0.99  --bmc1_ucm                              false
% 2.53/0.99  --bmc1_add_unsat_core                   none
% 2.53/0.99  --bmc1_unsat_core_children              false
% 2.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/0.99  --bmc1_out_stat                         full
% 2.53/0.99  --bmc1_ground_init                      false
% 2.53/0.99  --bmc1_pre_inst_next_state              false
% 2.53/0.99  --bmc1_pre_inst_state                   false
% 2.53/0.99  --bmc1_pre_inst_reach_state             false
% 2.53/0.99  --bmc1_out_unsat_core                   false
% 2.53/0.99  --bmc1_aig_witness_out                  false
% 2.53/0.99  --bmc1_verbose                          false
% 2.53/0.99  --bmc1_dump_clauses_tptp                false
% 2.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.53/0.99  --bmc1_dump_file                        -
% 2.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.53/0.99  --bmc1_ucm_extend_mode                  1
% 2.53/0.99  --bmc1_ucm_init_mode                    2
% 2.53/0.99  --bmc1_ucm_cone_mode                    none
% 2.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.53/0.99  --bmc1_ucm_relax_model                  4
% 2.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/0.99  --bmc1_ucm_layered_model                none
% 2.53/0.99  --bmc1_ucm_max_lemma_size               10
% 2.53/0.99  
% 2.53/0.99  ------ AIG Options
% 2.53/0.99  
% 2.53/0.99  --aig_mode                              false
% 2.53/0.99  
% 2.53/0.99  ------ Instantiation Options
% 2.53/0.99  
% 2.53/0.99  --instantiation_flag                    true
% 2.53/0.99  --inst_sos_flag                         false
% 2.53/0.99  --inst_sos_phase                        true
% 2.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel_side                     none
% 2.53/0.99  --inst_solver_per_active                1400
% 2.53/0.99  --inst_solver_calls_frac                1.
% 2.53/0.99  --inst_passive_queue_type               priority_queues
% 2.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/0.99  --inst_passive_queues_freq              [25;2]
% 2.53/0.99  --inst_dismatching                      true
% 2.53/0.99  --inst_eager_unprocessed_to_passive     true
% 2.53/0.99  --inst_prop_sim_given                   true
% 2.53/0.99  --inst_prop_sim_new                     false
% 2.53/0.99  --inst_subs_new                         false
% 2.53/0.99  --inst_eq_res_simp                      false
% 2.53/0.99  --inst_subs_given                       false
% 2.53/0.99  --inst_orphan_elimination               true
% 2.53/0.99  --inst_learning_loop_flag               true
% 2.53/0.99  --inst_learning_start                   3000
% 2.53/0.99  --inst_learning_factor                  2
% 2.53/0.99  --inst_start_prop_sim_after_learn       3
% 2.53/0.99  --inst_sel_renew                        solver
% 2.53/0.99  --inst_lit_activity_flag                true
% 2.53/0.99  --inst_restr_to_given                   false
% 2.53/0.99  --inst_activity_threshold               500
% 2.53/0.99  --inst_out_proof                        true
% 2.53/0.99  
% 2.53/0.99  ------ Resolution Options
% 2.53/0.99  
% 2.53/0.99  --resolution_flag                       false
% 2.53/0.99  --res_lit_sel                           adaptive
% 2.53/0.99  --res_lit_sel_side                      none
% 2.53/0.99  --res_ordering                          kbo
% 2.53/0.99  --res_to_prop_solver                    active
% 2.53/0.99  --res_prop_simpl_new                    false
% 2.53/0.99  --res_prop_simpl_given                  true
% 2.53/0.99  --res_passive_queue_type                priority_queues
% 2.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/0.99  --res_passive_queues_freq               [15;5]
% 2.53/0.99  --res_forward_subs                      full
% 2.53/0.99  --res_backward_subs                     full
% 2.53/0.99  --res_forward_subs_resolution           true
% 2.53/0.99  --res_backward_subs_resolution          true
% 2.53/0.99  --res_orphan_elimination                true
% 2.53/0.99  --res_time_limit                        2.
% 2.53/0.99  --res_out_proof                         true
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Options
% 2.53/0.99  
% 2.53/0.99  --superposition_flag                    true
% 2.53/0.99  --sup_passive_queue_type                priority_queues
% 2.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.53/0.99  --demod_completeness_check              fast
% 2.53/0.99  --demod_use_ground                      true
% 2.53/0.99  --sup_to_prop_solver                    passive
% 2.53/0.99  --sup_prop_simpl_new                    true
% 2.53/0.99  --sup_prop_simpl_given                  true
% 2.53/0.99  --sup_fun_splitting                     false
% 2.53/0.99  --sup_smt_interval                      50000
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Simplification Setup
% 2.53/0.99  
% 2.53/0.99  --sup_indices_passive                   []
% 2.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_full_bw                           [BwDemod]
% 2.53/0.99  --sup_immed_triv                        [TrivRules]
% 2.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_immed_bw_main                     []
% 2.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  
% 2.53/0.99  ------ Combination Options
% 2.53/0.99  
% 2.53/0.99  --comb_res_mult                         3
% 2.53/0.99  --comb_sup_mult                         2
% 2.53/0.99  --comb_inst_mult                        10
% 2.53/0.99  
% 2.53/0.99  ------ Debug Options
% 2.53/0.99  
% 2.53/0.99  --dbg_backtrace                         false
% 2.53/0.99  --dbg_dump_prop_clauses                 false
% 2.53/0.99  --dbg_dump_prop_clauses_file            -
% 2.53/0.99  --dbg_out_stat                          false
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  ------ Proving...
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  % SZS status Theorem for theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  fof(f3,axiom,(
% 2.53/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f18,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.53/0.99    inference(ennf_transformation,[],[f3])).
% 2.53/0.99  
% 2.53/0.99  fof(f37,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.53/0.99    inference(nnf_transformation,[],[f18])).
% 2.53/0.99  
% 2.53/0.99  fof(f46,plain,(
% 2.53/0.99    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f13,conjecture,(
% 2.53/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f14,negated_conjecture,(
% 2.53/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 2.53/0.99    inference(negated_conjecture,[],[f13])).
% 2.53/0.99  
% 2.53/0.99  fof(f35,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f14])).
% 2.53/0.99  
% 2.53/0.99  fof(f36,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f35])).
% 2.53/0.99  
% 2.53/0.99  fof(f39,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/0.99    inference(nnf_transformation,[],[f36])).
% 2.53/0.99  
% 2.53/0.99  fof(f40,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f39])).
% 2.53/0.99  
% 2.53/0.99  fof(f42,plain,(
% 2.53/0.99    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.53/0.99    introduced(choice_axiom,[])).
% 2.53/0.99  
% 2.53/0.99  fof(f41,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.53/0.99    introduced(choice_axiom,[])).
% 2.53/0.99  
% 2.53/0.99  fof(f43,plain,(
% 2.53/0.99    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 2.53/0.99  
% 2.53/0.99  fof(f65,plain,(
% 2.53/0.99    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 2.53/0.99    inference(cnf_transformation,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  fof(f63,plain,(
% 2.53/0.99    l1_pre_topc(sK0)),
% 2.53/0.99    inference(cnf_transformation,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  fof(f64,plain,(
% 2.53/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.53/0.99    inference(cnf_transformation,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  fof(f11,axiom,(
% 2.53/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f31,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f11])).
% 2.53/0.99  
% 2.53/0.99  fof(f32,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f31])).
% 2.53/0.99  
% 2.53/0.99  fof(f38,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(nnf_transformation,[],[f32])).
% 2.53/0.99  
% 2.53/0.99  fof(f57,plain,(
% 2.53/0.99    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f38])).
% 2.53/0.99  
% 2.53/0.99  fof(f61,plain,(
% 2.53/0.99    ~v2_struct_0(sK0)),
% 2.53/0.99    inference(cnf_transformation,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  fof(f62,plain,(
% 2.53/0.99    v2_pre_topc(sK0)),
% 2.53/0.99    inference(cnf_transformation,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  fof(f5,axiom,(
% 2.53/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f20,plain,(
% 2.53/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.53/0.99    inference(ennf_transformation,[],[f5])).
% 2.53/0.99  
% 2.53/0.99  fof(f49,plain,(
% 2.53/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f20])).
% 2.53/0.99  
% 2.53/0.99  fof(f4,axiom,(
% 2.53/0.99    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f19,plain,(
% 2.53/0.99    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.53/0.99    inference(ennf_transformation,[],[f4])).
% 2.53/0.99  
% 2.53/0.99  fof(f48,plain,(
% 2.53/0.99    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f19])).
% 2.53/0.99  
% 2.53/0.99  fof(f2,axiom,(
% 2.53/0.99    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f17,plain,(
% 2.53/1.00    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f2])).
% 2.53/1.00  
% 2.53/1.00  fof(f45,plain,(
% 2.53/1.00    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f17])).
% 2.53/1.00  
% 2.53/1.00  fof(f1,axiom,(
% 2.53/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f15,plain,(
% 2.53/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f1])).
% 2.53/1.00  
% 2.53/1.00  fof(f16,plain,(
% 2.53/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.53/1.00    inference(flattening,[],[f15])).
% 2.53/1.00  
% 2.53/1.00  fof(f44,plain,(
% 2.53/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f16])).
% 2.53/1.00  
% 2.53/1.00  fof(f10,axiom,(
% 2.53/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f29,plain,(
% 2.53/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f10])).
% 2.53/1.00  
% 2.53/1.00  fof(f30,plain,(
% 2.53/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f29])).
% 2.53/1.00  
% 2.53/1.00  fof(f54,plain,(
% 2.53/1.00    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f30])).
% 2.53/1.00  
% 2.53/1.00  fof(f56,plain,(
% 2.53/1.00    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f30])).
% 2.53/1.00  
% 2.53/1.00  fof(f12,axiom,(
% 2.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f33,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f12])).
% 2.53/1.00  
% 2.53/1.00  fof(f34,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f33])).
% 2.53/1.00  
% 2.53/1.00  fof(f59,plain,(
% 2.53/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f34])).
% 2.53/1.00  
% 2.53/1.00  fof(f7,axiom,(
% 2.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f23,plain,(
% 2.53/1.00    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f7])).
% 2.53/1.00  
% 2.53/1.00  fof(f24,plain,(
% 2.53/1.00    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.53/1.00    inference(flattening,[],[f23])).
% 2.53/1.00  
% 2.53/1.00  fof(f51,plain,(
% 2.53/1.00    ( ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f24])).
% 2.53/1.00  
% 2.53/1.00  fof(f6,axiom,(
% 2.53/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f21,plain,(
% 2.53/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f6])).
% 2.53/1.00  
% 2.53/1.00  fof(f22,plain,(
% 2.53/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.53/1.00    inference(flattening,[],[f21])).
% 2.53/1.00  
% 2.53/1.00  fof(f50,plain,(
% 2.53/1.00    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f22])).
% 2.53/1.00  
% 2.53/1.00  fof(f60,plain,(
% 2.53/1.00    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f34])).
% 2.53/1.00  
% 2.53/1.00  fof(f58,plain,(
% 2.53/1.00    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f38])).
% 2.53/1.00  
% 2.53/1.00  fof(f47,plain,(
% 2.53/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f37])).
% 2.53/1.00  
% 2.53/1.00  fof(f66,plain,(
% 2.53/1.00    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.53/1.00    inference(cnf_transformation,[],[f43])).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 2.53/1.00      | ~ v3_pre_topc(X0,X1)
% 2.53/1.00      | ~ l1_pre_topc(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_18,negated_conjecture,
% 2.53/1.00      ( v3_pre_topc(sK1,sK0)
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_177,plain,
% 2.53/1.00      ( v3_pre_topc(sK1,sK0)
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_408,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.53/1.00      | sK1 != X0
% 2.53/1.00      | sK0 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_177]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_409,plain,
% 2.53/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_408]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_20,negated_conjecture,
% 2.53/1.00      ( l1_pre_topc(sK0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_19,negated_conjecture,
% 2.53/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_411,plain,
% 2.53/1.00      ( r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_409,c_20,c_19]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_931,plain,
% 2.53/1.00      ( r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(prop_impl,[status(thm)],[c_20,c_19,c_409]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1180,plain,
% 2.53/1.00      ( r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_931]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1613,plain,
% 2.53/1.00      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.53/1.00      | r2_hidden(sK1,u1_pre_topc(sK0)) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1180]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1182,negated_conjecture,
% 2.53/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1611,plain,
% 2.53/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1182]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_14,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_22,negated_conjecture,
% 2.53/1.00      ( ~ v2_struct_0(sK0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_495,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 2.53/1.00      | sK0 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_496,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ r2_hidden(X0,u1_pre_topc(sK0))
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_495]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_21,negated_conjecture,
% 2.53/1.00      ( v2_pre_topc(sK0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_500,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ r2_hidden(X0,u1_pre_topc(sK0))
% 2.53/1.00      | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_496,c_21,c_20]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1177,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ r2_hidden(X0_47,u1_pre_topc(sK0))
% 2.53/1.00      | k5_tmap_1(sK0,X0_47) = u1_pre_topc(sK0) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_500]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1616,plain,
% 2.53/1.00      ( k5_tmap_1(sK0,X0_47) = u1_pre_topc(sK0)
% 2.53/1.00      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/1.00      | r2_hidden(X0_47,u1_pre_topc(sK0)) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1177]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2004,plain,
% 2.53/1.00      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/1.00      | r2_hidden(sK1,u1_pre_topc(sK0)) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1611,c_1616]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2054,plain,
% 2.53/1.00      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1613,c_2004]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_5,plain,
% 2.53/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4,plain,
% 2.53/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.00      | ~ l1_struct_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_306,plain,
% 2.53/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.00      | ~ l1_pre_topc(X0) ),
% 2.53/1.00      inference(resolution,[status(thm)],[c_5,c_4]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_723,plain,
% 2.53/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.00      | sK0 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_306,c_20]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_724,plain,
% 2.53/1.00      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_723]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1169,plain,
% 2.53/1.00      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_724]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1622,plain,
% 2.53/1.00      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1169]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1,plain,
% 2.53/1.00      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_317,plain,
% 2.53/1.00      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 2.53/1.00      inference(resolution,[status(thm)],[c_5,c_1]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_718,plain,
% 2.53/1.00      ( k2_struct_0(X0) = u1_struct_0(X0) | sK0 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_317,c_20]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_719,plain,
% 2.53/1.00      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_718]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1170,plain,
% 2.53/1.00      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_719]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1633,plain,
% 2.53/1.00      ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_1622,c_1170]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_0,plain,
% 2.53/1.00      ( ~ l1_pre_topc(X0)
% 2.53/1.00      | ~ v1_pre_topc(X0)
% 2.53/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.53/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_12,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | v1_pre_topc(k6_tmap_1(X1,X0)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_537,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | v1_pre_topc(k6_tmap_1(X1,X0))
% 2.53/1.00      | sK0 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_538,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_537]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_542,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_538,c_21,c_20]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_614,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | k6_tmap_1(sK0,X0) != X1
% 2.53/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_542]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_615,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ l1_pre_topc(k6_tmap_1(sK0,X0))
% 2.53/1.00      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_614]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_10,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_573,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | l1_pre_topc(k6_tmap_1(X1,X0))
% 2.53/1.00      | sK0 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_574,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | l1_pre_topc(k6_tmap_1(sK0,X0))
% 2.53/1.00      | ~ l1_pre_topc(sK0) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_573]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_619,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_615,c_21,c_20,c_574]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1175,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0_47)),u1_pre_topc(k6_tmap_1(sK0,X0_47))) = k6_tmap_1(sK0,X0_47) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_619]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1618,plain,
% 2.53/1.00      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0_47)),u1_pre_topc(k6_tmap_1(sK0,X0_47))) = k6_tmap_1(sK0,X0_47)
% 2.53/1.00      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2320,plain,
% 2.53/1.00      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1633,c_1618]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_16,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_459,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.53/1.00      | sK0 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_460,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_459]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_464,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_460,c_21,c_20]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1179,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | u1_struct_0(k6_tmap_1(sK0,X0_47)) = u1_struct_0(sK0) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_464]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1614,plain,
% 2.53/1.00      ( u1_struct_0(k6_tmap_1(sK0,X0_47)) = u1_struct_0(sK0)
% 2.53/1.00      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1179]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1750,plain,
% 2.53/1.00      ( u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1633,c_1614]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2322,plain,
% 2.53/1.00      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_2320,c_1750]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2005,plain,
% 2.53/1.00      ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(sK0)
% 2.53/1.00      | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1633,c_1616]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_7,plain,
% 2.53/1.00      ( ~ v2_pre_topc(X0)
% 2.53/1.00      | ~ l1_pre_topc(X0)
% 2.53/1.00      | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_635,plain,
% 2.53/1.00      ( ~ l1_pre_topc(X0)
% 2.53/1.00      | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
% 2.53/1.00      | sK0 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_636,plain,
% 2.53/1.00      ( ~ l1_pre_topc(sK0)
% 2.53/1.00      | k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_635]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_55,plain,
% 2.53/1.00      ( ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_638,plain,
% 2.53/1.00      ( k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_636,c_21,c_20,c_55]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1174,plain,
% 2.53/1.00      ( k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_638]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1630,plain,
% 2.53/1.00      ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_1174,c_1170]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_6,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | v3_pre_topc(k1_tops_1(X1,X0),X1)
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_373,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.53/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 2.53/1.00      | ~ v2_pre_topc(X3)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X3)
% 2.53/1.00      | X3 != X1
% 2.53/1.00      | k1_tops_1(X3,X2) != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_6]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_374,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | r2_hidden(k1_tops_1(X1,X0),u1_pre_topc(X1))
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_373]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_661,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | r2_hidden(k1_tops_1(X1,X0),u1_pre_topc(X1))
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | sK0 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_374,c_21]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_662,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0))
% 2.53/1.00      | ~ l1_pre_topc(sK0) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_661]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_666,plain,
% 2.53/1.00      ( r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0))
% 2.53/1.00      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_662,c_20]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_667,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0)) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_666]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1172,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ m1_subset_1(k1_tops_1(sK0,X0_47),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | r2_hidden(k1_tops_1(sK0,X0_47),u1_pre_topc(sK0)) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_667]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1620,plain,
% 2.53/1.00      ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/1.00      | m1_subset_1(k1_tops_1(sK0,X0_47),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/1.00      | r2_hidden(k1_tops_1(sK0,X0_47),u1_pre_topc(sK0)) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1172]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2161,plain,
% 2.53/1.00      ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/1.00      | r2_hidden(k1_tops_1(sK0,u1_struct_0(sK0)),u1_pre_topc(sK0)) = iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1630,c_1620]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2162,plain,
% 2.53/1.00      ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/1.00      | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) = iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_2161,c_1630]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2246,plain,
% 2.53/1.00      ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_2005,c_1633,c_2162]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_15,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_477,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 2.53/1.00      | sK0 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_478,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_477]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_482,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_478,c_21,c_20]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1178,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | u1_pre_topc(k6_tmap_1(sK0,X0_47)) = k5_tmap_1(sK0,X0_47) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_482]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1615,plain,
% 2.53/1.00      ( u1_pre_topc(k6_tmap_1(sK0,X0_47)) = k5_tmap_1(sK0,X0_47)
% 2.53/1.00      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1178]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1828,plain,
% 2.53/1.00      ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) = k5_tmap_1(sK0,u1_struct_0(sK0)) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1633,c_1615]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2249,plain,
% 2.53/1.00      ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) = u1_pre_topc(sK0) ),
% 2.53/1.00      inference(demodulation,[status(thm)],[c_2246,c_1828]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2915,plain,
% 2.53/1.00      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_2322,c_2249]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2929,plain,
% 2.53/1.00      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/1.00      | k6_tmap_1(sK0,u1_struct_0(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_2054,c_2915]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3076,plain,
% 2.53/1.00      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/1.00      | u1_pre_topc(k6_tmap_1(sK0,sK1)) = u1_pre_topc(sK0) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_2929,c_2249]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1827,plain,
% 2.53/1.00      ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1611,c_1615]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3080,plain,
% 2.53/1.00      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 2.53/1.00      inference(demodulation,[status(thm)],[c_3076,c_1827]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2319,plain,
% 2.53/1.00      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) = k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1611,c_1618]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1749,plain,
% 2.53/1.00      ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1611,c_1614]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2325,plain,
% 2.53/1.00      ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_2319,c_1749,c_1827]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3143,plain,
% 2.53/1.00      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(demodulation,[status(thm)],[c_3080,c_2325]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_13,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_516,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
% 2.53/1.00      | sK0 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_517,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | r2_hidden(X0,u1_pre_topc(sK0))
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_516]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_521,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | r2_hidden(X0,u1_pre_topc(sK0))
% 2.53/1.00      | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_517,c_21,c_20]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1176,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | r2_hidden(X0_47,u1_pre_topc(sK0))
% 2.53/1.00      | k5_tmap_1(sK0,X0_47) != u1_pre_topc(sK0) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_521]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1229,plain,
% 2.53/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/1.00      | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_1176]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.53/1.00      | v3_pre_topc(X0,X1)
% 2.53/1.00      | ~ l1_pre_topc(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_17,negated_conjecture,
% 2.53/1.00      ( ~ v3_pre_topc(sK1,sK0)
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_175,plain,
% 2.53/1.00      ( ~ v3_pre_topc(sK1,sK0)
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(prop_impl,[status(thm)],[c_17]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_394,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.53/1.00      | sK1 != X0
% 2.53/1.00      | sK0 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_175]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_395,plain,
% 2.53/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/1.00      | ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_394]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_397,plain,
% 2.53/1.00      ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_395,c_20,c_19]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_929,plain,
% 2.53/1.00      ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(prop_impl,[status(thm)],[c_20,c_19,c_395]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1181,plain,
% 2.53/1.00      ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/1.00      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_929]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(contradiction,plain,
% 2.53/1.00      ( $false ),
% 2.53/1.00      inference(minisat,[status(thm)],[c_3143,c_3080,c_1229,c_1181,c_19]) ).
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/1.00  
% 2.53/1.00  ------                               Statistics
% 2.53/1.00  
% 2.53/1.00  ------ General
% 2.53/1.00  
% 2.53/1.00  abstr_ref_over_cycles:                  0
% 2.53/1.00  abstr_ref_under_cycles:                 0
% 2.53/1.00  gc_basic_clause_elim:                   0
% 2.53/1.00  forced_gc_time:                         0
% 2.53/1.00  parsing_time:                           0.015
% 2.53/1.00  unif_index_cands_time:                  0.
% 2.53/1.00  unif_index_add_time:                    0.
% 2.53/1.00  orderings_time:                         0.
% 2.53/1.00  out_proof_time:                         0.012
% 2.53/1.00  total_time:                             0.128
% 2.53/1.00  num_of_symbols:                         51
% 2.53/1.00  num_of_terms:                           2257
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing
% 2.53/1.00  
% 2.53/1.00  num_of_splits:                          0
% 2.53/1.00  num_of_split_atoms:                     0
% 2.53/1.00  num_of_reused_defs:                     0
% 2.53/1.00  num_eq_ax_congr_red:                    10
% 2.53/1.00  num_of_sem_filtered_clauses:            1
% 2.53/1.00  num_of_subtypes:                        4
% 2.53/1.00  monotx_restored_types:                  0
% 2.53/1.00  sat_num_of_epr_types:                   0
% 2.53/1.00  sat_num_of_non_cyclic_types:            0
% 2.53/1.00  sat_guarded_non_collapsed_types:        0
% 2.53/1.00  num_pure_diseq_elim:                    0
% 2.53/1.00  simp_replaced_by:                       0
% 2.53/1.00  res_preprocessed:                       109
% 2.53/1.00  prep_upred:                             0
% 2.53/1.00  prep_unflattend:                        36
% 2.53/1.00  smt_new_axioms:                         0
% 2.53/1.00  pred_elim_cands:                        2
% 2.53/1.00  pred_elim:                              7
% 2.53/1.00  pred_elim_cl:                           6
% 2.53/1.00  pred_elim_cycles:                       10
% 2.53/1.00  merged_defs:                            8
% 2.53/1.00  merged_defs_ncl:                        0
% 2.53/1.00  bin_hyper_res:                          9
% 2.53/1.00  prep_cycles:                            4
% 2.53/1.00  pred_elim_time:                         0.014
% 2.53/1.00  splitting_time:                         0.
% 2.53/1.00  sem_filter_time:                        0.
% 2.53/1.00  monotx_time:                            0.
% 2.53/1.00  subtype_inf_time:                       0.
% 2.53/1.00  
% 2.53/1.00  ------ Problem properties
% 2.53/1.00  
% 2.53/1.00  clauses:                                17
% 2.53/1.00  conjectures:                            1
% 2.53/1.00  epr:                                    0
% 2.53/1.00  horn:                                   16
% 2.53/1.00  ground:                                 6
% 2.53/1.00  unary:                                  4
% 2.53/1.00  binary:                                 8
% 2.53/1.00  lits:                                   36
% 2.53/1.00  lits_eq:                                12
% 2.53/1.00  fd_pure:                                0
% 2.53/1.00  fd_pseudo:                              0
% 2.53/1.00  fd_cond:                                0
% 2.53/1.00  fd_pseudo_cond:                         0
% 2.53/1.00  ac_symbols:                             0
% 2.53/1.00  
% 2.53/1.00  ------ Propositional Solver
% 2.53/1.00  
% 2.53/1.00  prop_solver_calls:                      28
% 2.53/1.00  prop_fast_solver_calls:                 815
% 2.53/1.00  smt_solver_calls:                       0
% 2.53/1.00  smt_fast_solver_calls:                  0
% 2.53/1.00  prop_num_of_clauses:                    991
% 2.53/1.00  prop_preprocess_simplified:             3952
% 2.53/1.00  prop_fo_subsumed:                       40
% 2.53/1.00  prop_solver_time:                       0.
% 2.53/1.00  smt_solver_time:                        0.
% 2.53/1.00  smt_fast_solver_time:                   0.
% 2.53/1.00  prop_fast_solver_time:                  0.
% 2.53/1.00  prop_unsat_core_time:                   0.
% 2.53/1.00  
% 2.53/1.00  ------ QBF
% 2.53/1.00  
% 2.53/1.00  qbf_q_res:                              0
% 2.53/1.00  qbf_num_tautologies:                    0
% 2.53/1.00  qbf_prep_cycles:                        0
% 2.53/1.00  
% 2.53/1.00  ------ BMC1
% 2.53/1.00  
% 2.53/1.00  bmc1_current_bound:                     -1
% 2.53/1.00  bmc1_last_solved_bound:                 -1
% 2.53/1.00  bmc1_unsat_core_size:                   -1
% 2.53/1.00  bmc1_unsat_core_parents_size:           -1
% 2.53/1.00  bmc1_merge_next_fun:                    0
% 2.53/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.53/1.00  
% 2.53/1.00  ------ Instantiation
% 2.53/1.00  
% 2.53/1.00  inst_num_of_clauses:                    326
% 2.53/1.00  inst_num_in_passive:                    127
% 2.53/1.00  inst_num_in_active:                     171
% 2.53/1.00  inst_num_in_unprocessed:                28
% 2.53/1.00  inst_num_of_loops:                      200
% 2.53/1.00  inst_num_of_learning_restarts:          0
% 2.53/1.00  inst_num_moves_active_passive:          24
% 2.53/1.00  inst_lit_activity:                      0
% 2.53/1.00  inst_lit_activity_moves:                0
% 2.53/1.00  inst_num_tautologies:                   0
% 2.53/1.00  inst_num_prop_implied:                  0
% 2.53/1.00  inst_num_existing_simplified:           0
% 2.53/1.00  inst_num_eq_res_simplified:             0
% 2.53/1.00  inst_num_child_elim:                    0
% 2.53/1.00  inst_num_of_dismatching_blockings:      69
% 2.53/1.00  inst_num_of_non_proper_insts:           295
% 2.53/1.00  inst_num_of_duplicates:                 0
% 2.53/1.00  inst_inst_num_from_inst_to_res:         0
% 2.53/1.00  inst_dismatching_checking_time:         0.
% 2.53/1.00  
% 2.53/1.00  ------ Resolution
% 2.53/1.00  
% 2.53/1.00  res_num_of_clauses:                     0
% 2.53/1.00  res_num_in_passive:                     0
% 2.53/1.00  res_num_in_active:                      0
% 2.53/1.00  res_num_of_loops:                       113
% 2.53/1.00  res_forward_subset_subsumed:            43
% 2.53/1.00  res_backward_subset_subsumed:           2
% 2.53/1.00  res_forward_subsumed:                   3
% 2.53/1.00  res_backward_subsumed:                  0
% 2.53/1.00  res_forward_subsumption_resolution:     1
% 2.53/1.00  res_backward_subsumption_resolution:    0
% 2.53/1.00  res_clause_to_clause_subsumption:       74
% 2.53/1.00  res_orphan_elimination:                 0
% 2.53/1.00  res_tautology_del:                      65
% 2.53/1.00  res_num_eq_res_simplified:              0
% 2.53/1.00  res_num_sel_changes:                    0
% 2.53/1.00  res_moves_from_active_to_pass:          0
% 2.53/1.00  
% 2.53/1.00  ------ Superposition
% 2.53/1.00  
% 2.53/1.00  sup_time_total:                         0.
% 2.53/1.00  sup_time_generating:                    0.
% 2.53/1.00  sup_time_sim_full:                      0.
% 2.53/1.00  sup_time_sim_immed:                     0.
% 2.53/1.00  
% 2.53/1.00  sup_num_of_clauses:                     34
% 2.53/1.00  sup_num_in_active:                      27
% 2.53/1.00  sup_num_in_passive:                     7
% 2.53/1.00  sup_num_of_loops:                       38
% 2.53/1.00  sup_fw_superposition:                   24
% 2.53/1.00  sup_bw_superposition:                   13
% 2.53/1.00  sup_immediate_simplified:               20
% 2.53/1.00  sup_given_eliminated:                   0
% 2.53/1.00  comparisons_done:                       0
% 2.53/1.00  comparisons_avoided:                    6
% 2.53/1.00  
% 2.53/1.00  ------ Simplifications
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  sim_fw_subset_subsumed:                 4
% 2.53/1.00  sim_bw_subset_subsumed:                 4
% 2.53/1.00  sim_fw_subsumed:                        3
% 2.53/1.00  sim_bw_subsumed:                        0
% 2.53/1.00  sim_fw_subsumption_res:                 0
% 2.53/1.00  sim_bw_subsumption_res:                 0
% 2.53/1.00  sim_tautology_del:                      1
% 2.53/1.00  sim_eq_tautology_del:                   0
% 2.53/1.00  sim_eq_res_simp:                        0
% 2.53/1.00  sim_fw_demodulated:                     1
% 2.53/1.00  sim_bw_demodulated:                     8
% 2.53/1.00  sim_light_normalised:                   17
% 2.53/1.00  sim_joinable_taut:                      0
% 2.53/1.00  sim_joinable_simp:                      0
% 2.53/1.00  sim_ac_normalised:                      0
% 2.53/1.00  sim_smt_subsumption:                    0
% 2.53/1.00  
%------------------------------------------------------------------------------
