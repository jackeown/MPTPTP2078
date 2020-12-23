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
% DateTime   : Thu Dec  3 12:23:52 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  182 (1554 expanded)
%              Number of clauses        :  114 ( 353 expanded)
%              Number of leaves         :   14 ( 348 expanded)
%              Depth                    :   26
%              Number of atoms          :  704 (9518 expanded)
%              Number of equality atoms :  195 (2265 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

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
    inference(nnf_transformation,[],[f32])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f69,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_199,plain,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_199])).

cnf(c_352,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_354,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_352,c_23,c_22])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X1) != u1_pre_topc(sK0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_354])).

cnf(c_401,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_443,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_24])).

cnf(c_444,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_446,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_25,c_23,c_22])).

cnf(c_811,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_446])).

cnf(c_846,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_811])).

cnf(c_12,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_561,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_562,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_566,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_562,c_25,c_23])).

cnf(c_1491,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v1_tops_2(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_2122,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top
    | v1_tops_2(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_1491])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(u1_pre_topc(X1),k5_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(u1_pre_topc(X1),k5_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_25,c_23])).

cnf(c_1631,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1660,plain,
    ( ~ r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
    | ~ r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1501,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( v1_tops_2(X0,X1)
    | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_603,plain,
    ( v1_tops_2(X0,X1)
    | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_604,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_608,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_604,c_25,c_23])).

cnf(c_1489,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_tops_2(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_2197,plain,
    ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_1489])).

cnf(c_28,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_71,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_73,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1650,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1651,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1650])).

cnf(c_1653,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_7,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1666,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1747,plain,
    ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1666])).

cnf(c_1750,plain,
    ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top
    | r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1747])).

cnf(c_1749,plain,
    ( ~ v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_1752,plain,
    ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) = iProver_top
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1749])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1665,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1818,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(instantiation,[status(thm)],[c_1665])).

cnf(c_1819,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1818])).

cnf(c_2275,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2276,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2275])).

cnf(c_2294,plain,
    ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2197,c_28,c_73,c_1653,c_1750,c_1752,c_1819,c_2276])).

cnf(c_2299,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v1_tops_2(u1_pre_topc(k6_tmap_1(sK0,sK1)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_2294])).

cnf(c_1498,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_507,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_25,c_23])).

cnf(c_1494,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_1693,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1498,c_1494])).

cnf(c_2300,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v1_tops_2(k5_tmap_1(sK0,sK1),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2299,c_1693])).

cnf(c_2301,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2300])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_25,c_23])).

cnf(c_1495,plain,
    ( u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_1658,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1498,c_1495])).

cnf(c_1926,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1658,c_1501])).

cnf(c_1929,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1926,c_1693])).

cnf(c_29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_25,c_23])).

cnf(c_1637,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_1638,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1637])).

cnf(c_2288,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1929,c_29,c_1638])).

cnf(c_8,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1499,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2383,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),sK0) != iProver_top
    | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2288,c_1499])).

cnf(c_2427,plain,
    ( ~ v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
    | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2383])).

cnf(c_2710,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2122,c_23,c_22,c_1631,c_1660,c_2301,c_2427])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_25,c_23])).

cnf(c_1492,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_1732,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1498,c_1492])).

cnf(c_2714,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2710,c_1732])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_197,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_197])).

cnf(c_338,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_340,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_23,c_22])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X1) != u1_pre_topc(sK0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_340])).

cnf(c_374,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_457,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_374,c_24])).

cnf(c_458,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_460,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_25,c_23,c_22])).

cnf(c_810,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_460])).

cnf(c_844,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_810])).

cnf(c_2715,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(demodulation,[status(thm)],[c_2710,c_844])).

cnf(c_2719,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_2715])).

cnf(c_2723,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2714,c_2719])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.29/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/0.99  
% 2.29/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.29/0.99  
% 2.29/0.99  ------  iProver source info
% 2.29/0.99  
% 2.29/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.29/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.29/0.99  git: non_committed_changes: false
% 2.29/0.99  git: last_make_outside_of_git: false
% 2.29/0.99  
% 2.29/0.99  ------ 
% 2.29/0.99  
% 2.29/0.99  ------ Input Options
% 2.29/0.99  
% 2.29/0.99  --out_options                           all
% 2.29/0.99  --tptp_safe_out                         true
% 2.29/0.99  --problem_path                          ""
% 2.29/0.99  --include_path                          ""
% 2.29/0.99  --clausifier                            res/vclausify_rel
% 2.29/0.99  --clausifier_options                    --mode clausify
% 2.29/0.99  --stdin                                 false
% 2.29/0.99  --stats_out                             all
% 2.29/0.99  
% 2.29/0.99  ------ General Options
% 2.29/0.99  
% 2.29/0.99  --fof                                   false
% 2.29/0.99  --time_out_real                         305.
% 2.29/0.99  --time_out_virtual                      -1.
% 2.29/0.99  --symbol_type_check                     false
% 2.29/0.99  --clausify_out                          false
% 2.29/0.99  --sig_cnt_out                           false
% 2.29/0.99  --trig_cnt_out                          false
% 2.29/0.99  --trig_cnt_out_tolerance                1.
% 2.29/0.99  --trig_cnt_out_sk_spl                   false
% 2.29/0.99  --abstr_cl_out                          false
% 2.29/0.99  
% 2.29/0.99  ------ Global Options
% 2.29/0.99  
% 2.29/0.99  --schedule                              default
% 2.29/0.99  --add_important_lit                     false
% 2.29/0.99  --prop_solver_per_cl                    1000
% 2.29/0.99  --min_unsat_core                        false
% 2.29/0.99  --soft_assumptions                      false
% 2.29/0.99  --soft_lemma_size                       3
% 2.29/0.99  --prop_impl_unit_size                   0
% 2.29/0.99  --prop_impl_unit                        []
% 2.29/0.99  --share_sel_clauses                     true
% 2.29/0.99  --reset_solvers                         false
% 2.29/0.99  --bc_imp_inh                            [conj_cone]
% 2.29/0.99  --conj_cone_tolerance                   3.
% 2.29/0.99  --extra_neg_conj                        none
% 2.29/0.99  --large_theory_mode                     true
% 2.29/0.99  --prolific_symb_bound                   200
% 2.29/0.99  --lt_threshold                          2000
% 2.29/0.99  --clause_weak_htbl                      true
% 2.29/0.99  --gc_record_bc_elim                     false
% 2.29/0.99  
% 2.29/0.99  ------ Preprocessing Options
% 2.29/0.99  
% 2.29/0.99  --preprocessing_flag                    true
% 2.29/0.99  --time_out_prep_mult                    0.1
% 2.29/0.99  --splitting_mode                        input
% 2.29/0.99  --splitting_grd                         true
% 2.29/0.99  --splitting_cvd                         false
% 2.29/0.99  --splitting_cvd_svl                     false
% 2.29/0.99  --splitting_nvd                         32
% 2.29/0.99  --sub_typing                            true
% 2.29/0.99  --prep_gs_sim                           true
% 2.29/0.99  --prep_unflatten                        true
% 2.29/0.99  --prep_res_sim                          true
% 2.29/0.99  --prep_upred                            true
% 2.29/0.99  --prep_sem_filter                       exhaustive
% 2.29/0.99  --prep_sem_filter_out                   false
% 2.29/0.99  --pred_elim                             true
% 2.29/0.99  --res_sim_input                         true
% 2.29/0.99  --eq_ax_congr_red                       true
% 2.29/0.99  --pure_diseq_elim                       true
% 2.29/0.99  --brand_transform                       false
% 2.29/0.99  --non_eq_to_eq                          false
% 2.29/0.99  --prep_def_merge                        true
% 2.29/0.99  --prep_def_merge_prop_impl              false
% 2.29/0.99  --prep_def_merge_mbd                    true
% 2.29/0.99  --prep_def_merge_tr_red                 false
% 2.29/0.99  --prep_def_merge_tr_cl                  false
% 2.29/0.99  --smt_preprocessing                     true
% 2.29/0.99  --smt_ac_axioms                         fast
% 2.29/0.99  --preprocessed_out                      false
% 2.29/0.99  --preprocessed_stats                    false
% 2.29/0.99  
% 2.29/0.99  ------ Abstraction refinement Options
% 2.29/0.99  
% 2.29/0.99  --abstr_ref                             []
% 2.29/0.99  --abstr_ref_prep                        false
% 2.29/0.99  --abstr_ref_until_sat                   false
% 2.29/0.99  --abstr_ref_sig_restrict                funpre
% 2.29/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.29/0.99  --abstr_ref_under                       []
% 2.29/0.99  
% 2.29/0.99  ------ SAT Options
% 2.29/0.99  
% 2.29/0.99  --sat_mode                              false
% 2.29/0.99  --sat_fm_restart_options                ""
% 2.29/0.99  --sat_gr_def                            false
% 2.29/0.99  --sat_epr_types                         true
% 2.29/0.99  --sat_non_cyclic_types                  false
% 2.29/0.99  --sat_finite_models                     false
% 2.29/0.99  --sat_fm_lemmas                         false
% 2.29/0.99  --sat_fm_prep                           false
% 2.29/0.99  --sat_fm_uc_incr                        true
% 2.29/0.99  --sat_out_model                         small
% 2.29/0.99  --sat_out_clauses                       false
% 2.29/0.99  
% 2.29/0.99  ------ QBF Options
% 2.29/0.99  
% 2.29/0.99  --qbf_mode                              false
% 2.29/0.99  --qbf_elim_univ                         false
% 2.29/0.99  --qbf_dom_inst                          none
% 2.29/0.99  --qbf_dom_pre_inst                      false
% 2.29/0.99  --qbf_sk_in                             false
% 2.29/0.99  --qbf_pred_elim                         true
% 2.29/0.99  --qbf_split                             512
% 2.29/0.99  
% 2.29/0.99  ------ BMC1 Options
% 2.29/0.99  
% 2.29/0.99  --bmc1_incremental                      false
% 2.29/0.99  --bmc1_axioms                           reachable_all
% 2.29/0.99  --bmc1_min_bound                        0
% 2.29/0.99  --bmc1_max_bound                        -1
% 2.29/0.99  --bmc1_max_bound_default                -1
% 2.29/0.99  --bmc1_symbol_reachability              true
% 2.29/0.99  --bmc1_property_lemmas                  false
% 2.29/0.99  --bmc1_k_induction                      false
% 2.29/0.99  --bmc1_non_equiv_states                 false
% 2.29/0.99  --bmc1_deadlock                         false
% 2.29/0.99  --bmc1_ucm                              false
% 2.29/0.99  --bmc1_add_unsat_core                   none
% 2.29/0.99  --bmc1_unsat_core_children              false
% 2.29/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.29/0.99  --bmc1_out_stat                         full
% 2.29/0.99  --bmc1_ground_init                      false
% 2.29/0.99  --bmc1_pre_inst_next_state              false
% 2.29/0.99  --bmc1_pre_inst_state                   false
% 2.29/0.99  --bmc1_pre_inst_reach_state             false
% 2.29/0.99  --bmc1_out_unsat_core                   false
% 2.29/0.99  --bmc1_aig_witness_out                  false
% 2.29/0.99  --bmc1_verbose                          false
% 2.29/0.99  --bmc1_dump_clauses_tptp                false
% 2.29/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.29/0.99  --bmc1_dump_file                        -
% 2.29/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.29/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.29/0.99  --bmc1_ucm_extend_mode                  1
% 2.29/0.99  --bmc1_ucm_init_mode                    2
% 2.29/0.99  --bmc1_ucm_cone_mode                    none
% 2.29/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.29/0.99  --bmc1_ucm_relax_model                  4
% 2.29/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.29/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.29/0.99  --bmc1_ucm_layered_model                none
% 2.29/0.99  --bmc1_ucm_max_lemma_size               10
% 2.29/0.99  
% 2.29/0.99  ------ AIG Options
% 2.29/0.99  
% 2.29/0.99  --aig_mode                              false
% 2.29/0.99  
% 2.29/0.99  ------ Instantiation Options
% 2.29/0.99  
% 2.29/0.99  --instantiation_flag                    true
% 2.29/0.99  --inst_sos_flag                         false
% 2.29/0.99  --inst_sos_phase                        true
% 2.29/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.29/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.29/0.99  --inst_lit_sel_side                     num_symb
% 2.29/0.99  --inst_solver_per_active                1400
% 2.29/0.99  --inst_solver_calls_frac                1.
% 2.29/0.99  --inst_passive_queue_type               priority_queues
% 2.29/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.29/0.99  --inst_passive_queues_freq              [25;2]
% 2.29/0.99  --inst_dismatching                      true
% 2.29/0.99  --inst_eager_unprocessed_to_passive     true
% 2.29/0.99  --inst_prop_sim_given                   true
% 2.29/0.99  --inst_prop_sim_new                     false
% 2.29/0.99  --inst_subs_new                         false
% 2.29/0.99  --inst_eq_res_simp                      false
% 2.29/0.99  --inst_subs_given                       false
% 2.29/0.99  --inst_orphan_elimination               true
% 2.29/0.99  --inst_learning_loop_flag               true
% 2.29/0.99  --inst_learning_start                   3000
% 2.29/0.99  --inst_learning_factor                  2
% 2.29/0.99  --inst_start_prop_sim_after_learn       3
% 2.29/0.99  --inst_sel_renew                        solver
% 2.29/0.99  --inst_lit_activity_flag                true
% 2.29/0.99  --inst_restr_to_given                   false
% 2.29/0.99  --inst_activity_threshold               500
% 2.29/0.99  --inst_out_proof                        true
% 2.29/0.99  
% 2.29/0.99  ------ Resolution Options
% 2.29/0.99  
% 2.29/0.99  --resolution_flag                       true
% 2.29/0.99  --res_lit_sel                           adaptive
% 2.29/0.99  --res_lit_sel_side                      none
% 2.29/0.99  --res_ordering                          kbo
% 2.29/0.99  --res_to_prop_solver                    active
% 2.29/0.99  --res_prop_simpl_new                    false
% 2.29/0.99  --res_prop_simpl_given                  true
% 2.29/0.99  --res_passive_queue_type                priority_queues
% 2.29/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.29/0.99  --res_passive_queues_freq               [15;5]
% 2.29/0.99  --res_forward_subs                      full
% 2.29/0.99  --res_backward_subs                     full
% 2.29/0.99  --res_forward_subs_resolution           true
% 2.29/0.99  --res_backward_subs_resolution          true
% 2.29/0.99  --res_orphan_elimination                true
% 2.29/0.99  --res_time_limit                        2.
% 2.29/0.99  --res_out_proof                         true
% 2.29/0.99  
% 2.29/0.99  ------ Superposition Options
% 2.29/0.99  
% 2.29/0.99  --superposition_flag                    true
% 2.29/0.99  --sup_passive_queue_type                priority_queues
% 2.29/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.29/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.29/0.99  --demod_completeness_check              fast
% 2.29/0.99  --demod_use_ground                      true
% 2.29/0.99  --sup_to_prop_solver                    passive
% 2.29/0.99  --sup_prop_simpl_new                    true
% 2.29/0.99  --sup_prop_simpl_given                  true
% 2.29/0.99  --sup_fun_splitting                     false
% 2.29/0.99  --sup_smt_interval                      50000
% 2.29/0.99  
% 2.29/0.99  ------ Superposition Simplification Setup
% 2.29/0.99  
% 2.29/0.99  --sup_indices_passive                   []
% 2.29/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.29/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/0.99  --sup_full_bw                           [BwDemod]
% 2.29/0.99  --sup_immed_triv                        [TrivRules]
% 2.29/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.29/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/0.99  --sup_immed_bw_main                     []
% 2.29/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.29/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/0.99  
% 2.29/0.99  ------ Combination Options
% 2.29/0.99  
% 2.29/0.99  --comb_res_mult                         3
% 2.29/0.99  --comb_sup_mult                         2
% 2.29/0.99  --comb_inst_mult                        10
% 2.29/0.99  
% 2.29/0.99  ------ Debug Options
% 2.29/0.99  
% 2.29/0.99  --dbg_backtrace                         false
% 2.29/0.99  --dbg_dump_prop_clauses                 false
% 2.29/0.99  --dbg_dump_prop_clauses_file            -
% 2.29/0.99  --dbg_out_stat                          false
% 2.29/0.99  ------ Parsing...
% 2.29/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.29/0.99  
% 2.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.29/0.99  
% 2.29/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.29/0.99  
% 2.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.29/0.99  ------ Proving...
% 2.29/0.99  ------ Problem Properties 
% 2.29/0.99  
% 2.29/0.99  
% 2.29/0.99  clauses                                 19
% 2.29/0.99  conjectures                             2
% 2.29/0.99  EPR                                     3
% 2.29/0.99  Horn                                    18
% 2.29/0.99  unary                                   3
% 2.29/0.99  binary                                  9
% 2.29/0.99  lits                                    44
% 2.29/0.99  lits eq                                 8
% 2.29/0.99  fd_pure                                 0
% 2.29/0.99  fd_pseudo                               0
% 2.29/0.99  fd_cond                                 0
% 2.29/0.99  fd_pseudo_cond                          1
% 2.29/0.99  AC symbols                              0
% 2.29/0.99  
% 2.29/0.99  ------ Schedule dynamic 5 is on 
% 2.29/0.99  
% 2.29/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.29/0.99  
% 2.29/0.99  
% 2.29/0.99  ------ 
% 2.29/0.99  Current options:
% 2.29/0.99  ------ 
% 2.29/0.99  
% 2.29/0.99  ------ Input Options
% 2.29/0.99  
% 2.29/0.99  --out_options                           all
% 2.29/0.99  --tptp_safe_out                         true
% 2.29/0.99  --problem_path                          ""
% 2.29/0.99  --include_path                          ""
% 2.29/0.99  --clausifier                            res/vclausify_rel
% 2.29/0.99  --clausifier_options                    --mode clausify
% 2.29/0.99  --stdin                                 false
% 2.29/0.99  --stats_out                             all
% 2.29/0.99  
% 2.29/0.99  ------ General Options
% 2.29/0.99  
% 2.29/0.99  --fof                                   false
% 2.29/0.99  --time_out_real                         305.
% 2.29/0.99  --time_out_virtual                      -1.
% 2.29/0.99  --symbol_type_check                     false
% 2.29/0.99  --clausify_out                          false
% 2.29/0.99  --sig_cnt_out                           false
% 2.29/0.99  --trig_cnt_out                          false
% 2.29/0.99  --trig_cnt_out_tolerance                1.
% 2.29/0.99  --trig_cnt_out_sk_spl                   false
% 2.29/0.99  --abstr_cl_out                          false
% 2.29/0.99  
% 2.29/0.99  ------ Global Options
% 2.29/0.99  
% 2.29/0.99  --schedule                              default
% 2.29/0.99  --add_important_lit                     false
% 2.29/0.99  --prop_solver_per_cl                    1000
% 2.29/0.99  --min_unsat_core                        false
% 2.29/0.99  --soft_assumptions                      false
% 2.29/0.99  --soft_lemma_size                       3
% 2.29/0.99  --prop_impl_unit_size                   0
% 2.29/0.99  --prop_impl_unit                        []
% 2.29/0.99  --share_sel_clauses                     true
% 2.29/0.99  --reset_solvers                         false
% 2.29/0.99  --bc_imp_inh                            [conj_cone]
% 2.29/0.99  --conj_cone_tolerance                   3.
% 2.29/0.99  --extra_neg_conj                        none
% 2.29/0.99  --large_theory_mode                     true
% 2.29/0.99  --prolific_symb_bound                   200
% 2.29/0.99  --lt_threshold                          2000
% 2.29/0.99  --clause_weak_htbl                      true
% 2.29/0.99  --gc_record_bc_elim                     false
% 2.29/0.99  
% 2.29/0.99  ------ Preprocessing Options
% 2.29/0.99  
% 2.29/0.99  --preprocessing_flag                    true
% 2.29/0.99  --time_out_prep_mult                    0.1
% 2.29/0.99  --splitting_mode                        input
% 2.29/0.99  --splitting_grd                         true
% 2.29/0.99  --splitting_cvd                         false
% 2.29/0.99  --splitting_cvd_svl                     false
% 2.29/0.99  --splitting_nvd                         32
% 2.29/0.99  --sub_typing                            true
% 2.29/0.99  --prep_gs_sim                           true
% 2.29/0.99  --prep_unflatten                        true
% 2.29/0.99  --prep_res_sim                          true
% 2.29/0.99  --prep_upred                            true
% 2.29/0.99  --prep_sem_filter                       exhaustive
% 2.29/0.99  --prep_sem_filter_out                   false
% 2.29/0.99  --pred_elim                             true
% 2.29/0.99  --res_sim_input                         true
% 2.29/0.99  --eq_ax_congr_red                       true
% 2.29/0.99  --pure_diseq_elim                       true
% 2.29/0.99  --brand_transform                       false
% 2.29/0.99  --non_eq_to_eq                          false
% 2.29/0.99  --prep_def_merge                        true
% 2.29/0.99  --prep_def_merge_prop_impl              false
% 2.29/0.99  --prep_def_merge_mbd                    true
% 2.29/0.99  --prep_def_merge_tr_red                 false
% 2.29/0.99  --prep_def_merge_tr_cl                  false
% 2.29/0.99  --smt_preprocessing                     true
% 2.29/0.99  --smt_ac_axioms                         fast
% 2.29/0.99  --preprocessed_out                      false
% 2.29/0.99  --preprocessed_stats                    false
% 2.29/0.99  
% 2.29/0.99  ------ Abstraction refinement Options
% 2.29/0.99  
% 2.29/0.99  --abstr_ref                             []
% 2.29/0.99  --abstr_ref_prep                        false
% 2.29/0.99  --abstr_ref_until_sat                   false
% 2.29/0.99  --abstr_ref_sig_restrict                funpre
% 2.29/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.29/0.99  --abstr_ref_under                       []
% 2.29/0.99  
% 2.29/0.99  ------ SAT Options
% 2.29/0.99  
% 2.29/0.99  --sat_mode                              false
% 2.29/0.99  --sat_fm_restart_options                ""
% 2.29/0.99  --sat_gr_def                            false
% 2.29/0.99  --sat_epr_types                         true
% 2.29/0.99  --sat_non_cyclic_types                  false
% 2.29/0.99  --sat_finite_models                     false
% 2.29/0.99  --sat_fm_lemmas                         false
% 2.29/0.99  --sat_fm_prep                           false
% 2.29/0.99  --sat_fm_uc_incr                        true
% 2.29/0.99  --sat_out_model                         small
% 2.29/0.99  --sat_out_clauses                       false
% 2.29/0.99  
% 2.29/0.99  ------ QBF Options
% 2.29/0.99  
% 2.29/0.99  --qbf_mode                              false
% 2.29/0.99  --qbf_elim_univ                         false
% 2.29/0.99  --qbf_dom_inst                          none
% 2.29/0.99  --qbf_dom_pre_inst                      false
% 2.29/0.99  --qbf_sk_in                             false
% 2.29/0.99  --qbf_pred_elim                         true
% 2.29/0.99  --qbf_split                             512
% 2.29/0.99  
% 2.29/0.99  ------ BMC1 Options
% 2.29/0.99  
% 2.29/0.99  --bmc1_incremental                      false
% 2.29/0.99  --bmc1_axioms                           reachable_all
% 2.29/0.99  --bmc1_min_bound                        0
% 2.29/0.99  --bmc1_max_bound                        -1
% 2.29/0.99  --bmc1_max_bound_default                -1
% 2.29/0.99  --bmc1_symbol_reachability              true
% 2.29/0.99  --bmc1_property_lemmas                  false
% 2.29/0.99  --bmc1_k_induction                      false
% 2.29/0.99  --bmc1_non_equiv_states                 false
% 2.29/0.99  --bmc1_deadlock                         false
% 2.29/0.99  --bmc1_ucm                              false
% 2.29/0.99  --bmc1_add_unsat_core                   none
% 2.29/0.99  --bmc1_unsat_core_children              false
% 2.29/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.29/0.99  --bmc1_out_stat                         full
% 2.29/0.99  --bmc1_ground_init                      false
% 2.29/0.99  --bmc1_pre_inst_next_state              false
% 2.29/0.99  --bmc1_pre_inst_state                   false
% 2.29/0.99  --bmc1_pre_inst_reach_state             false
% 2.29/0.99  --bmc1_out_unsat_core                   false
% 2.29/0.99  --bmc1_aig_witness_out                  false
% 2.29/0.99  --bmc1_verbose                          false
% 2.29/0.99  --bmc1_dump_clauses_tptp                false
% 2.29/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.29/0.99  --bmc1_dump_file                        -
% 2.29/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.29/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.29/0.99  --bmc1_ucm_extend_mode                  1
% 2.29/0.99  --bmc1_ucm_init_mode                    2
% 2.29/0.99  --bmc1_ucm_cone_mode                    none
% 2.29/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.29/0.99  --bmc1_ucm_relax_model                  4
% 2.29/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.29/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.29/0.99  --bmc1_ucm_layered_model                none
% 2.29/0.99  --bmc1_ucm_max_lemma_size               10
% 2.29/0.99  
% 2.29/0.99  ------ AIG Options
% 2.29/0.99  
% 2.29/0.99  --aig_mode                              false
% 2.29/0.99  
% 2.29/0.99  ------ Instantiation Options
% 2.29/0.99  
% 2.29/0.99  --instantiation_flag                    true
% 2.29/0.99  --inst_sos_flag                         false
% 2.29/0.99  --inst_sos_phase                        true
% 2.29/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.29/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.29/0.99  --inst_lit_sel_side                     none
% 2.29/0.99  --inst_solver_per_active                1400
% 2.29/0.99  --inst_solver_calls_frac                1.
% 2.29/0.99  --inst_passive_queue_type               priority_queues
% 2.29/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.29/0.99  --inst_passive_queues_freq              [25;2]
% 2.29/0.99  --inst_dismatching                      true
% 2.29/0.99  --inst_eager_unprocessed_to_passive     true
% 2.29/0.99  --inst_prop_sim_given                   true
% 2.29/0.99  --inst_prop_sim_new                     false
% 2.29/0.99  --inst_subs_new                         false
% 2.29/0.99  --inst_eq_res_simp                      false
% 2.29/0.99  --inst_subs_given                       false
% 2.29/0.99  --inst_orphan_elimination               true
% 2.29/0.99  --inst_learning_loop_flag               true
% 2.29/0.99  --inst_learning_start                   3000
% 2.29/0.99  --inst_learning_factor                  2
% 2.29/0.99  --inst_start_prop_sim_after_learn       3
% 2.29/0.99  --inst_sel_renew                        solver
% 2.29/0.99  --inst_lit_activity_flag                true
% 2.29/0.99  --inst_restr_to_given                   false
% 2.29/0.99  --inst_activity_threshold               500
% 2.29/0.99  --inst_out_proof                        true
% 2.29/0.99  
% 2.29/0.99  ------ Resolution Options
% 2.29/0.99  
% 2.29/0.99  --resolution_flag                       false
% 2.29/0.99  --res_lit_sel                           adaptive
% 2.29/0.99  --res_lit_sel_side                      none
% 2.29/0.99  --res_ordering                          kbo
% 2.29/0.99  --res_to_prop_solver                    active
% 2.29/0.99  --res_prop_simpl_new                    false
% 2.29/0.99  --res_prop_simpl_given                  true
% 2.29/0.99  --res_passive_queue_type                priority_queues
% 2.29/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.29/0.99  --res_passive_queues_freq               [15;5]
% 2.29/0.99  --res_forward_subs                      full
% 2.29/0.99  --res_backward_subs                     full
% 2.29/0.99  --res_forward_subs_resolution           true
% 2.29/0.99  --res_backward_subs_resolution          true
% 2.29/0.99  --res_orphan_elimination                true
% 2.29/0.99  --res_time_limit                        2.
% 2.29/0.99  --res_out_proof                         true
% 2.29/0.99  
% 2.29/0.99  ------ Superposition Options
% 2.29/0.99  
% 2.29/0.99  --superposition_flag                    true
% 2.29/0.99  --sup_passive_queue_type                priority_queues
% 2.29/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.29/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.29/0.99  --demod_completeness_check              fast
% 2.29/0.99  --demod_use_ground                      true
% 2.29/0.99  --sup_to_prop_solver                    passive
% 2.29/0.99  --sup_prop_simpl_new                    true
% 2.29/0.99  --sup_prop_simpl_given                  true
% 2.29/0.99  --sup_fun_splitting                     false
% 2.29/0.99  --sup_smt_interval                      50000
% 2.29/0.99  
% 2.29/0.99  ------ Superposition Simplification Setup
% 2.29/0.99  
% 2.29/0.99  --sup_indices_passive                   []
% 2.29/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.29/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/0.99  --sup_full_bw                           [BwDemod]
% 2.29/0.99  --sup_immed_triv                        [TrivRules]
% 2.29/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.29/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/0.99  --sup_immed_bw_main                     []
% 2.29/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.29/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/0.99  
% 2.29/0.99  ------ Combination Options
% 2.29/0.99  
% 2.29/0.99  --comb_res_mult                         3
% 2.29/0.99  --comb_sup_mult                         2
% 2.29/0.99  --comb_inst_mult                        10
% 2.29/0.99  
% 2.29/0.99  ------ Debug Options
% 2.29/0.99  
% 2.29/0.99  --dbg_backtrace                         false
% 2.29/0.99  --dbg_dump_prop_clauses                 false
% 2.29/0.99  --dbg_dump_prop_clauses_file            -
% 2.29/0.99  --dbg_out_stat                          false
% 2.29/0.99  
% 2.29/0.99  
% 2.29/0.99  
% 2.29/0.99  
% 2.29/0.99  ------ Proving...
% 2.29/0.99  
% 2.29/0.99  
% 2.29/0.99  % SZS status Theorem for theBenchmark.p
% 2.29/0.99  
% 2.29/0.99   Resolution empty clause
% 2.29/0.99  
% 2.29/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.29/0.99  
% 2.29/0.99  fof(f9,axiom,(
% 2.29/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f25,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.29/0.99    inference(ennf_transformation,[],[f9])).
% 2.29/0.99  
% 2.29/0.99  fof(f26,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.29/0.99    inference(flattening,[],[f25])).
% 2.29/0.99  
% 2.29/0.99  fof(f39,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.29/0.99    inference(nnf_transformation,[],[f26])).
% 2.29/0.99  
% 2.29/0.99  fof(f60,plain,(
% 2.29/0.99    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f39])).
% 2.29/0.99  
% 2.29/0.99  fof(f2,axiom,(
% 2.29/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f15,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.29/0.99    inference(ennf_transformation,[],[f2])).
% 2.29/0.99  
% 2.29/0.99  fof(f35,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.29/0.99    inference(nnf_transformation,[],[f15])).
% 2.29/0.99  
% 2.29/0.99  fof(f48,plain,(
% 2.29/0.99    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f35])).
% 2.29/0.99  
% 2.29/0.99  fof(f12,conjecture,(
% 2.29/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f13,negated_conjecture,(
% 2.29/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 2.29/0.99    inference(negated_conjecture,[],[f12])).
% 2.29/0.99  
% 2.29/0.99  fof(f31,plain,(
% 2.29/0.99    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.29/0.99    inference(ennf_transformation,[],[f13])).
% 2.29/0.99  
% 2.29/0.99  fof(f32,plain,(
% 2.29/0.99    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.29/0.99    inference(flattening,[],[f31])).
% 2.29/0.99  
% 2.29/0.99  fof(f40,plain,(
% 2.29/0.99    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.29/0.99    inference(nnf_transformation,[],[f32])).
% 2.29/0.99  
% 2.29/0.99  fof(f41,plain,(
% 2.29/0.99    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.29/0.99    inference(flattening,[],[f40])).
% 2.29/0.99  
% 2.29/0.99  fof(f43,plain,(
% 2.29/0.99    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.29/0.99    introduced(choice_axiom,[])).
% 2.29/0.99  
% 2.29/0.99  fof(f42,plain,(
% 2.29/0.99    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.29/0.99    introduced(choice_axiom,[])).
% 2.29/0.99  
% 2.29/0.99  fof(f44,plain,(
% 2.29/0.99    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 2.29/0.99  
% 2.29/0.99  fof(f69,plain,(
% 2.29/0.99    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 2.29/0.99    inference(cnf_transformation,[],[f44])).
% 2.29/0.99  
% 2.29/0.99  fof(f67,plain,(
% 2.29/0.99    l1_pre_topc(sK0)),
% 2.29/0.99    inference(cnf_transformation,[],[f44])).
% 2.29/0.99  
% 2.29/0.99  fof(f68,plain,(
% 2.29/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.29/0.99    inference(cnf_transformation,[],[f44])).
% 2.29/0.99  
% 2.29/0.99  fof(f66,plain,(
% 2.29/0.99    v2_pre_topc(sK0)),
% 2.29/0.99    inference(cnf_transformation,[],[f44])).
% 2.29/0.99  
% 2.29/0.99  fof(f65,plain,(
% 2.29/0.99    ~v2_struct_0(sK0)),
% 2.29/0.99    inference(cnf_transformation,[],[f44])).
% 2.29/0.99  
% 2.29/0.99  fof(f6,axiom,(
% 2.29/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f19,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.29/0.99    inference(ennf_transformation,[],[f6])).
% 2.29/0.99  
% 2.29/0.99  fof(f20,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.29/0.99    inference(flattening,[],[f19])).
% 2.29/0.99  
% 2.29/0.99  fof(f37,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.29/0.99    inference(nnf_transformation,[],[f20])).
% 2.29/0.99  
% 2.29/0.99  fof(f38,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.29/0.99    inference(flattening,[],[f37])).
% 2.29/0.99  
% 2.29/0.99  fof(f54,plain,(
% 2.29/0.99    ( ! [X0,X1] : (v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f38])).
% 2.29/0.99  
% 2.29/0.99  fof(f11,axiom,(
% 2.29/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f29,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : (r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.29/0.99    inference(ennf_transformation,[],[f11])).
% 2.29/0.99  
% 2.29/0.99  fof(f30,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : (r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.29/0.99    inference(flattening,[],[f29])).
% 2.29/0.99  
% 2.29/0.99  fof(f64,plain,(
% 2.29/0.99    ( ! [X0,X1] : (r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f30])).
% 2.29/0.99  
% 2.29/0.99  fof(f1,axiom,(
% 2.29/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f33,plain,(
% 2.29/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.29/0.99    inference(nnf_transformation,[],[f1])).
% 2.29/0.99  
% 2.29/0.99  fof(f34,plain,(
% 2.29/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.29/0.99    inference(flattening,[],[f33])).
% 2.29/0.99  
% 2.29/0.99  fof(f47,plain,(
% 2.29/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f34])).
% 2.29/0.99  
% 2.29/0.99  fof(f4,axiom,(
% 2.29/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f17,plain,(
% 2.29/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.29/0.99    inference(ennf_transformation,[],[f4])).
% 2.29/0.99  
% 2.29/0.99  fof(f51,plain,(
% 2.29/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f17])).
% 2.29/0.99  
% 2.29/0.99  fof(f56,plain,(
% 2.29/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f38])).
% 2.29/0.99  
% 2.29/0.99  fof(f3,axiom,(
% 2.29/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f14,plain,(
% 2.29/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 2.29/0.99    inference(pure_predicate_removal,[],[f3])).
% 2.29/0.99  
% 2.29/0.99  fof(f16,plain,(
% 2.29/0.99    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.29/0.99    inference(ennf_transformation,[],[f14])).
% 2.29/0.99  
% 2.29/0.99  fof(f50,plain,(
% 2.29/0.99    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.29/0.99    inference(cnf_transformation,[],[f16])).
% 2.29/0.99  
% 2.29/0.99  fof(f5,axiom,(
% 2.29/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f18,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.29/0.99    inference(ennf_transformation,[],[f5])).
% 2.29/0.99  
% 2.29/0.99  fof(f36,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.29/0.99    inference(nnf_transformation,[],[f18])).
% 2.29/0.99  
% 2.29/0.99  fof(f53,plain,(
% 2.29/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f36])).
% 2.29/0.99  
% 2.29/0.99  fof(f45,plain,(
% 2.29/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.29/0.99    inference(cnf_transformation,[],[f34])).
% 2.29/0.99  
% 2.29/0.99  fof(f72,plain,(
% 2.29/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.29/0.99    inference(equality_resolution,[],[f45])).
% 2.29/0.99  
% 2.29/0.99  fof(f10,axiom,(
% 2.29/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f27,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.29/0.99    inference(ennf_transformation,[],[f10])).
% 2.29/0.99  
% 2.29/0.99  fof(f28,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.29/0.99    inference(flattening,[],[f27])).
% 2.29/0.99  
% 2.29/0.99  fof(f63,plain,(
% 2.29/0.99    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f28])).
% 2.29/0.99  
% 2.29/0.99  fof(f62,plain,(
% 2.29/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f28])).
% 2.29/0.99  
% 2.29/0.99  fof(f8,axiom,(
% 2.29/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f23,plain,(
% 2.29/0.99    ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.29/0.99    inference(ennf_transformation,[],[f8])).
% 2.29/0.99  
% 2.29/0.99  fof(f24,plain,(
% 2.29/0.99    ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.29/0.99    inference(flattening,[],[f23])).
% 2.29/0.99  
% 2.29/0.99  fof(f59,plain,(
% 2.29/0.99    ( ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f24])).
% 2.29/0.99  
% 2.29/0.99  fof(f52,plain,(
% 2.29/0.99    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f36])).
% 2.29/0.99  
% 2.29/0.99  fof(f7,axiom,(
% 2.29/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)))),
% 2.29/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/0.99  
% 2.29/0.99  fof(f21,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.29/0.99    inference(ennf_transformation,[],[f7])).
% 2.29/0.99  
% 2.29/0.99  fof(f22,plain,(
% 2.29/0.99    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.29/0.99    inference(flattening,[],[f21])).
% 2.29/0.99  
% 2.29/0.99  fof(f58,plain,(
% 2.29/0.99    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f22])).
% 2.29/0.99  
% 2.29/0.99  fof(f61,plain,(
% 2.29/0.99    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f39])).
% 2.29/0.99  
% 2.29/0.99  fof(f49,plain,(
% 2.29/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.29/0.99    inference(cnf_transformation,[],[f35])).
% 2.29/0.99  
% 2.29/0.99  fof(f70,plain,(
% 2.29/0.99    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.29/0.99    inference(cnf_transformation,[],[f44])).
% 2.29/0.99  
% 2.29/0.99  cnf(c_16,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ v2_pre_topc(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_4,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | r2_hidden(X0,u1_pre_topc(X1))
% 2.29/0.99      | ~ v3_pre_topc(X0,X1)
% 2.29/0.99      | ~ l1_pre_topc(X1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_21,negated_conjecture,
% 2.29/0.99      ( v3_pre_topc(sK1,sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_199,plain,
% 2.29/0.99      ( v3_pre_topc(sK1,sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_351,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | r2_hidden(X0,u1_pre_topc(X1))
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.29/0.99      | sK1 != X0
% 2.29/0.99      | sK0 != X1 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_199]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_352,plain,
% 2.29/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | r2_hidden(sK1,u1_pre_topc(sK0))
% 2.29/0.99      | ~ l1_pre_topc(sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_351]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_23,negated_conjecture,
% 2.29/0.99      ( l1_pre_topc(sK0) ),
% 2.29/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_22,negated_conjecture,
% 2.29/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.29/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_354,plain,
% 2.29/0.99      ( r2_hidden(sK1,u1_pre_topc(sK0))
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_352,c_23,c_22]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_400,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ v2_pre_topc(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.29/0.99      | u1_pre_topc(X1) != u1_pre_topc(sK0)
% 2.29/0.99      | sK1 != X0 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_354]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_401,plain,
% 2.29/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.29/0.99      | v2_struct_0(X0)
% 2.29/0.99      | ~ v2_pre_topc(X0)
% 2.29/0.99      | ~ l1_pre_topc(X0)
% 2.29/0.99      | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.29/0.99      | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_400]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_24,negated_conjecture,
% 2.29/0.99      ( v2_pre_topc(sK0) ),
% 2.29/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_443,plain,
% 2.29/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.29/0.99      | v2_struct_0(X0)
% 2.29/0.99      | ~ l1_pre_topc(X0)
% 2.29/0.99      | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.29/0.99      | u1_pre_topc(X0) != u1_pre_topc(sK0)
% 2.29/0.99      | sK0 != X0 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_401,c_24]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_444,plain,
% 2.29/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | v2_struct_0(sK0)
% 2.29/0.99      | ~ l1_pre_topc(sK0)
% 2.29/0.99      | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.29/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_25,negated_conjecture,
% 2.29/0.99      ( ~ v2_struct_0(sK0) ),
% 2.29/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_446,plain,
% 2.29/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.29/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_444,c_25,c_23,c_22]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_811,plain,
% 2.29/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(equality_resolution_simp,[status(thm)],[c_446]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_846,plain,
% 2.29/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(prop_impl,[status(thm)],[c_811]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_12,plain,
% 2.29/0.99      ( ~ v1_tops_2(X0,X1)
% 2.29/0.99      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ v2_pre_topc(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_561,plain,
% 2.29/0.99      ( ~ v1_tops_2(X0,X1)
% 2.29/0.99      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | sK0 != X1 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_562,plain,
% 2.29/0.99      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.29/0.99      | ~ v1_tops_2(X0,sK0)
% 2.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.29/0.99      | v2_struct_0(sK0)
% 2.29/0.99      | ~ l1_pre_topc(sK0) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_561]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_566,plain,
% 2.29/0.99      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.29/0.99      | ~ v1_tops_2(X0,sK0)
% 2.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_562,c_25,c_23]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1491,plain,
% 2.29/0.99      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 2.29/0.99      | v1_tops_2(X0,sK0) != iProver_top
% 2.29/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2122,plain,
% 2.29/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.29/0.99      | v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top
% 2.29/0.99      | v1_tops_2(X0,sK0) != iProver_top
% 2.29/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 2.29/0.99      inference(superposition,[status(thm)],[c_846,c_1491]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_19,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | r1_tarski(u1_pre_topc(X1),k5_tmap_1(X1,X0))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ v2_pre_topc(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_471,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | r1_tarski(u1_pre_topc(X1),k5_tmap_1(X1,X0))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | sK0 != X1 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_472,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X0))
% 2.29/0.99      | v2_struct_0(sK0)
% 2.29/0.99      | ~ l1_pre_topc(sK0) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_471]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_476,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X0)) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_472,c_25,c_23]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1631,plain,
% 2.29/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_476]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_0,plain,
% 2.29/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.29/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1660,plain,
% 2.29/0.99      ( ~ r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
% 2.29/0.99      | ~ r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))
% 2.29/0.99      | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_6,plain,
% 2.29/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.29/0.99      | ~ l1_pre_topc(X0) ),
% 2.29/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1501,plain,
% 2.29/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.29/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_10,plain,
% 2.29/0.99      ( v1_tops_2(X0,X1)
% 2.29/0.99      | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ v2_pre_topc(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_603,plain,
% 2.29/0.99      ( v1_tops_2(X0,X1)
% 2.29/0.99      | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | sK0 != X1 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_604,plain,
% 2.29/0.99      ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.29/0.99      | v1_tops_2(X0,sK0)
% 2.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 2.29/0.99      | v2_struct_0(sK0)
% 2.29/0.99      | ~ l1_pre_topc(sK0) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_603]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_608,plain,
% 2.29/0.99      ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.29/0.99      | v1_tops_2(X0,sK0)
% 2.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_604,c_25,c_23]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1489,plain,
% 2.29/0.99      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.29/0.99      | v1_tops_2(X0,sK0) = iProver_top
% 2.29/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2197,plain,
% 2.29/0.99      ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.29/0.99      | v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) = iProver_top
% 2.29/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 2.29/0.99      inference(superposition,[status(thm)],[c_1501,c_1489]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_28,plain,
% 2.29/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_71,plain,
% 2.29/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.29/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_73,plain,
% 2.29/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.29/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_71]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_5,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.29/0.99      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 2.29/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1650,plain,
% 2.29/0.99      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.29/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1651,plain,
% 2.29/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 2.29/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1650]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1653,plain,
% 2.29/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.29/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_1651]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_7,plain,
% 2.29/0.99      ( v1_tops_2(X0,X1)
% 2.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.29/0.99      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 2.29/0.99      | ~ l1_pre_topc(X1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1666,plain,
% 2.29/0.99      ( v1_tops_2(u1_pre_topc(X0),X0)
% 2.29/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.29/0.99      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
% 2.29/0.99      | ~ l1_pre_topc(X0) ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1747,plain,
% 2.29/0.99      ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.29/0.99      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 2.29/0.99      | ~ r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
% 2.29/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_1666]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1750,plain,
% 2.29/0.99      ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 2.29/0.99      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top
% 2.29/0.99      | r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
% 2.29/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1747]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1749,plain,
% 2.29/0.99      ( ~ v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.29/0.99      | v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
% 2.29/0.99      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_608]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1752,plain,
% 2.29/0.99      ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.29/0.99      | v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) = iProver_top
% 2.29/0.99      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1749]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f72]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1665,plain,
% 2.29/0.99      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1818,plain,
% 2.29/0.99      ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_1665]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1819,plain,
% 2.29/0.99      ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1818]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2275,plain,
% 2.29/0.99      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 2.29/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2276,plain,
% 2.29/0.99      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = iProver_top
% 2.29/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_2275]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2294,plain,
% 2.29/0.99      ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) = iProver_top ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_2197,c_28,c_73,c_1653,c_1750,c_1752,c_1819,c_2276]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2299,plain,
% 2.29/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.29/0.99      | v1_tops_2(u1_pre_topc(k6_tmap_1(sK0,sK1)),sK0) = iProver_top ),
% 2.29/0.99      inference(superposition,[status(thm)],[c_846,c_2294]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1498,plain,
% 2.29/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_17,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ v2_pre_topc(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 2.29/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_507,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 2.29/0.99      | sK0 != X1 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_508,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | v2_struct_0(sK0)
% 2.29/0.99      | ~ l1_pre_topc(sK0)
% 2.29/0.99      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_507]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_512,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_508,c_25,c_23]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1494,plain,
% 2.29/0.99      ( u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0)
% 2.29/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1693,plain,
% 2.29/0.99      ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(superposition,[status(thm)],[c_1498,c_1494]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2300,plain,
% 2.29/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.29/0.99      | v1_tops_2(k5_tmap_1(sK0,sK1),sK0) = iProver_top ),
% 2.29/0.99      inference(light_normalisation,[status(thm)],[c_2299,c_1693]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2301,plain,
% 2.29/0.99      ( v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
% 2.29/0.99      | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 2.29/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2300]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_18,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ v2_pre_topc(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_489,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.29/0.99      | sK0 != X1 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_490,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | v2_struct_0(sK0)
% 2.29/0.99      | ~ l1_pre_topc(sK0)
% 2.29/0.99      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_489]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_494,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_490,c_25,c_23]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1495,plain,
% 2.29/0.99      ( u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0)
% 2.29/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1658,plain,
% 2.29/0.99      ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
% 2.29/0.99      inference(superposition,[status(thm)],[c_1498,c_1495]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1926,plain,
% 2.29/0.99      ( m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.29/0.99      | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
% 2.29/0.99      inference(superposition,[status(thm)],[c_1658,c_1501]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1929,plain,
% 2.29/0.99      ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.29/0.99      | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
% 2.29/0.99      inference(light_normalisation,[status(thm)],[c_1926,c_1693]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_29,plain,
% 2.29/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_14,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ v2_pre_topc(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_525,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | sK0 != X1 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_526,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.29/0.99      | v2_struct_0(sK0)
% 2.29/0.99      | ~ l1_pre_topc(sK0) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_525]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_530,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_526,c_25,c_23]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1637,plain,
% 2.29/0.99      ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.29/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.29/0.99      inference(instantiation,[status(thm)],[c_530]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1638,plain,
% 2.29/0.99      ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.29/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1637]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2288,plain,
% 2.29/0.99      ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_1929,c_29,c_1638]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_8,plain,
% 2.29/0.99      ( ~ v1_tops_2(X0,X1)
% 2.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.29/0.99      | r1_tarski(X0,u1_pre_topc(X1))
% 2.29/0.99      | ~ l1_pre_topc(X1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1499,plain,
% 2.29/0.99      ( v1_tops_2(X0,X1) != iProver_top
% 2.29/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 2.29/0.99      | r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
% 2.29/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2383,plain,
% 2.29/0.99      ( v1_tops_2(k5_tmap_1(sK0,sK1),sK0) != iProver_top
% 2.29/0.99      | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) = iProver_top
% 2.29/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.29/0.99      inference(superposition,[status(thm)],[c_2288,c_1499]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2427,plain,
% 2.29/0.99      ( ~ v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
% 2.29/0.99      | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
% 2.29/0.99      | ~ l1_pre_topc(sK0) ),
% 2.29/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2383]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2710,plain,
% 2.29/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_2122,c_23,c_22,c_1631,c_1660,c_2301,c_2427]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_13,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ v2_pre_topc(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
% 2.29/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_543,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
% 2.29/0.99      | sK0 != X1 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_544,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | v2_struct_0(sK0)
% 2.29/0.99      | ~ l1_pre_topc(sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_543]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_548,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_544,c_25,c_23]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1492,plain,
% 2.29/0.99      ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0)
% 2.29/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.29/0.99      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_1732,plain,
% 2.29/0.99      ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(superposition,[status(thm)],[c_1498,c_1492]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2714,plain,
% 2.29/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(demodulation,[status(thm)],[c_2710,c_1732]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_15,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | r2_hidden(X0,u1_pre_topc(X1))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ v2_pre_topc(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_3,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.29/0.99      | v3_pre_topc(X0,X1)
% 2.29/0.99      | ~ l1_pre_topc(X1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_20,negated_conjecture,
% 2.29/0.99      ( ~ v3_pre_topc(sK1,sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_197,plain,
% 2.29/0.99      ( ~ v3_pre_topc(sK1,sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(prop_impl,[status(thm)],[c_20]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_337,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.29/0.99      | sK1 != X0
% 2.29/0.99      | sK0 != X1 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_197]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_338,plain,
% 2.29/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 2.29/0.99      | ~ l1_pre_topc(sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_337]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_340,plain,
% 2.29/0.99      ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_338,c_23,c_22]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_373,plain,
% 2.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.29/0.99      | v2_struct_0(X1)
% 2.29/0.99      | ~ v2_pre_topc(X1)
% 2.29/0.99      | ~ l1_pre_topc(X1)
% 2.29/0.99      | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.29/0.99      | u1_pre_topc(X1) != u1_pre_topc(sK0)
% 2.29/0.99      | sK1 != X0 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_340]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_374,plain,
% 2.29/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.29/0.99      | v2_struct_0(X0)
% 2.29/0.99      | ~ v2_pre_topc(X0)
% 2.29/0.99      | ~ l1_pre_topc(X0)
% 2.29/0.99      | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.29/0.99      | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_373]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_457,plain,
% 2.29/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.29/0.99      | v2_struct_0(X0)
% 2.29/0.99      | ~ l1_pre_topc(X0)
% 2.29/0.99      | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.29/0.99      | u1_pre_topc(X0) != u1_pre_topc(sK0)
% 2.29/0.99      | sK0 != X0 ),
% 2.29/0.99      inference(resolution_lifted,[status(thm)],[c_374,c_24]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_458,plain,
% 2.29/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.29/0.99      | v2_struct_0(sK0)
% 2.29/0.99      | ~ l1_pre_topc(sK0)
% 2.29/0.99      | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.29/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.29/0.99      inference(unflattening,[status(thm)],[c_457]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_460,plain,
% 2.29/0.99      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.29/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.29/0.99      inference(global_propositional_subsumption,
% 2.29/0.99                [status(thm)],
% 2.29/0.99                [c_458,c_25,c_23,c_22]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_810,plain,
% 2.29/0.99      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(equality_resolution_simp,[status(thm)],[c_460]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_844,plain,
% 2.29/0.99      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 2.29/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(prop_impl,[status(thm)],[c_810]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2715,plain,
% 2.29/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.29/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.29/0.99      inference(demodulation,[status(thm)],[c_2710,c_844]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2719,plain,
% 2.29/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.29/0.99      inference(equality_resolution_simp,[status(thm)],[c_2715]) ).
% 2.29/0.99  
% 2.29/0.99  cnf(c_2723,plain,
% 2.29/0.99      ( $false ),
% 2.29/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2714,c_2719]) ).
% 2.29/0.99  
% 2.29/0.99  
% 2.29/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.29/0.99  
% 2.29/0.99  ------                               Statistics
% 2.29/0.99  
% 2.29/0.99  ------ General
% 2.29/0.99  
% 2.29/0.99  abstr_ref_over_cycles:                  0
% 2.29/0.99  abstr_ref_under_cycles:                 0
% 2.29/0.99  gc_basic_clause_elim:                   0
% 2.29/0.99  forced_gc_time:                         0
% 2.29/0.99  parsing_time:                           0.011
% 2.29/0.99  unif_index_cands_time:                  0.
% 2.29/0.99  unif_index_add_time:                    0.
% 2.29/0.99  orderings_time:                         0.
% 2.29/0.99  out_proof_time:                         0.014
% 2.29/0.99  total_time:                             0.095
% 2.29/0.99  num_of_symbols:                         47
% 2.29/0.99  num_of_terms:                           1582
% 2.29/0.99  
% 2.29/0.99  ------ Preprocessing
% 2.29/0.99  
% 2.29/0.99  num_of_splits:                          0
% 2.29/0.99  num_of_split_atoms:                     0
% 2.29/0.99  num_of_reused_defs:                     0
% 2.29/0.99  num_eq_ax_congr_red:                    6
% 2.29/0.99  num_of_sem_filtered_clauses:            1
% 2.29/0.99  num_of_subtypes:                        0
% 2.29/0.99  monotx_restored_types:                  0
% 2.29/0.99  sat_num_of_epr_types:                   0
% 2.29/0.99  sat_num_of_non_cyclic_types:            0
% 2.29/0.99  sat_guarded_non_collapsed_types:        0
% 2.29/0.99  num_pure_diseq_elim:                    0
% 2.29/0.99  simp_replaced_by:                       0
% 2.29/0.99  res_preprocessed:                       107
% 2.29/0.99  prep_upred:                             0
% 2.29/0.99  prep_unflattend:                        29
% 2.29/0.99  smt_new_axioms:                         0
% 2.29/0.99  pred_elim_cands:                        4
% 2.29/0.99  pred_elim:                              4
% 2.29/0.99  pred_elim_cl:                           6
% 2.29/0.99  pred_elim_cycles:                       6
% 2.29/0.99  merged_defs:                            8
% 2.29/0.99  merged_defs_ncl:                        0
% 2.29/0.99  bin_hyper_res:                          8
% 2.29/0.99  prep_cycles:                            4
% 2.29/0.99  pred_elim_time:                         0.01
% 2.29/0.99  splitting_time:                         0.
% 2.29/0.99  sem_filter_time:                        0.
% 2.29/0.99  monotx_time:                            0.
% 2.29/0.99  subtype_inf_time:                       0.
% 2.29/0.99  
% 2.29/0.99  ------ Problem properties
% 2.29/0.99  
% 2.29/0.99  clauses:                                19
% 2.29/0.99  conjectures:                            2
% 2.29/0.99  epr:                                    3
% 2.29/0.99  horn:                                   18
% 2.29/0.99  ground:                                 4
% 2.29/0.99  unary:                                  3
% 2.29/0.99  binary:                                 9
% 2.29/0.99  lits:                                   44
% 2.29/0.99  lits_eq:                                8
% 2.29/0.99  fd_pure:                                0
% 2.29/0.99  fd_pseudo:                              0
% 2.29/0.99  fd_cond:                                0
% 2.29/0.99  fd_pseudo_cond:                         1
% 2.29/0.99  ac_symbols:                             0
% 2.29/0.99  
% 2.29/0.99  ------ Propositional Solver
% 2.29/0.99  
% 2.29/0.99  prop_solver_calls:                      25
% 2.29/0.99  prop_fast_solver_calls:                 784
% 2.29/0.99  smt_solver_calls:                       0
% 2.29/0.99  smt_fast_solver_calls:                  0
% 2.29/0.99  prop_num_of_clauses:                    702
% 2.29/0.99  prop_preprocess_simplified:             3638
% 2.29/0.99  prop_fo_subsumed:                       34
% 2.29/0.99  prop_solver_time:                       0.
% 2.29/0.99  smt_solver_time:                        0.
% 2.29/0.99  smt_fast_solver_time:                   0.
% 2.29/0.99  prop_fast_solver_time:                  0.
% 2.29/0.99  prop_unsat_core_time:                   0.
% 2.29/0.99  
% 2.29/0.99  ------ QBF
% 2.29/0.99  
% 2.29/0.99  qbf_q_res:                              0
% 2.29/0.99  qbf_num_tautologies:                    0
% 2.29/0.99  qbf_prep_cycles:                        0
% 2.29/0.99  
% 2.29/0.99  ------ BMC1
% 2.29/0.99  
% 2.29/0.99  bmc1_current_bound:                     -1
% 2.29/0.99  bmc1_last_solved_bound:                 -1
% 2.29/0.99  bmc1_unsat_core_size:                   -1
% 2.29/0.99  bmc1_unsat_core_parents_size:           -1
% 2.29/0.99  bmc1_merge_next_fun:                    0
% 2.29/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.29/0.99  
% 2.29/0.99  ------ Instantiation
% 2.29/0.99  
% 2.29/0.99  inst_num_of_clauses:                    202
% 2.29/0.99  inst_num_in_passive:                    15
% 2.29/0.99  inst_num_in_active:                     125
% 2.29/0.99  inst_num_in_unprocessed:                62
% 2.29/0.99  inst_num_of_loops:                      130
% 2.29/0.99  inst_num_of_learning_restarts:          0
% 2.29/0.99  inst_num_moves_active_passive:          3
% 2.29/0.99  inst_lit_activity:                      0
% 2.29/0.99  inst_lit_activity_moves:                0
% 2.29/0.99  inst_num_tautologies:                   0
% 2.29/0.99  inst_num_prop_implied:                  0
% 2.29/0.99  inst_num_existing_simplified:           0
% 2.29/0.99  inst_num_eq_res_simplified:             0
% 2.29/0.99  inst_num_child_elim:                    0
% 2.29/0.99  inst_num_of_dismatching_blockings:      75
% 2.29/0.99  inst_num_of_non_proper_insts:           179
% 2.29/0.99  inst_num_of_duplicates:                 0
% 2.29/0.99  inst_inst_num_from_inst_to_res:         0
% 2.29/0.99  inst_dismatching_checking_time:         0.
% 2.29/0.99  
% 2.29/0.99  ------ Resolution
% 2.29/0.99  
% 2.29/0.99  res_num_of_clauses:                     0
% 2.29/0.99  res_num_in_passive:                     0
% 2.29/0.99  res_num_in_active:                      0
% 2.29/0.99  res_num_of_loops:                       111
% 2.29/0.99  res_forward_subset_subsumed:            12
% 2.29/0.99  res_backward_subset_subsumed:           0
% 2.29/0.99  res_forward_subsumed:                   0
% 2.29/0.99  res_backward_subsumed:                  0
% 2.29/0.99  res_forward_subsumption_resolution:     0
% 2.29/0.99  res_backward_subsumption_resolution:    0
% 2.29/0.99  res_clause_to_clause_subsumption:       100
% 2.29/0.99  res_orphan_elimination:                 0
% 2.29/0.99  res_tautology_del:                      39
% 2.29/0.99  res_num_eq_res_simplified:              2
% 2.29/0.99  res_num_sel_changes:                    0
% 2.29/0.99  res_moves_from_active_to_pass:          0
% 2.29/0.99  
% 2.29/0.99  ------ Superposition
% 2.29/0.99  
% 2.29/0.99  sup_time_total:                         0.
% 2.29/0.99  sup_time_generating:                    0.
% 2.29/0.99  sup_time_sim_full:                      0.
% 2.29/0.99  sup_time_sim_immed:                     0.
% 2.29/0.99  
% 2.29/0.99  sup_num_of_clauses:                     35
% 2.29/0.99  sup_num_in_active:                      19
% 2.29/0.99  sup_num_in_passive:                     16
% 2.29/0.99  sup_num_of_loops:                       24
% 2.29/0.99  sup_fw_superposition:                   30
% 2.29/0.99  sup_bw_superposition:                   1
% 2.29/0.99  sup_immediate_simplified:               11
% 2.29/0.99  sup_given_eliminated:                   0
% 2.29/0.99  comparisons_done:                       0
% 2.29/0.99  comparisons_avoided:                    3
% 2.29/0.99  
% 2.29/0.99  ------ Simplifications
% 2.29/0.99  
% 2.29/0.99  
% 2.29/0.99  sim_fw_subset_subsumed:                 1
% 2.29/0.99  sim_bw_subset_subsumed:                 3
% 2.29/0.99  sim_fw_subsumed:                        1
% 2.29/0.99  sim_bw_subsumed:                        0
% 2.29/0.99  sim_fw_subsumption_res:                 1
% 2.29/0.99  sim_bw_subsumption_res:                 0
% 2.29/0.99  sim_tautology_del:                      5
% 2.29/0.99  sim_eq_tautology_del:                   1
% 2.29/0.99  sim_eq_res_simp:                        1
% 2.29/0.99  sim_fw_demodulated:                     0
% 2.29/0.99  sim_bw_demodulated:                     4
% 2.29/0.99  sim_light_normalised:                   9
% 2.29/0.99  sim_joinable_taut:                      0
% 2.29/0.99  sim_joinable_simp:                      0
% 2.29/0.99  sim_ac_normalised:                      0
% 2.29/0.99  sim_smt_subsumption:                    0
% 2.29/0.99  
%------------------------------------------------------------------------------
