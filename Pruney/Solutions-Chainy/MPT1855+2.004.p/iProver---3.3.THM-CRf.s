%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:46 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  163 (1173 expanded)
%              Number of clauses        :  107 ( 401 expanded)
%              Number of leaves         :   15 ( 258 expanded)
%              Depth                    :   27
%              Number of atoms          :  650 (6087 expanded)
%              Number of equality atoms :  278 (1256 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_pre_topc(sK2,X0)
        & v7_struct_0(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_pre_topc(X1,sK1)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    & m1_pre_topc(sK2,sK1)
    & v7_struct_0(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f36,f35])).

fof(f56,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0))
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    v7_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f45,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_776,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1213,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_298,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_8])).

cnf(c_770,plain,
    ( m1_subset_1(sK0(X0_47),u1_struct_0(X0_47))
    | ~ v7_struct_0(X0_47)
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_298])).

cnf(c_1219,plain,
    ( m1_subset_1(sK0(X0_47),u1_struct_0(X0_47)) = iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_784,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_47))
    | m1_subset_1(X0_45,u1_struct_0(X1_47))
    | ~ m1_pre_topc(X0_47,X1_47)
    | v2_struct_0(X1_47)
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1205,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_47)) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(X1_47)) = iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_1730,plain,
    ( m1_subset_1(sK0(X0_47),u1_struct_0(X1_47)) = iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1205])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_785,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_825,plain,
    ( m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_2049,plain,
    ( l1_pre_topc(X1_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_subset_1(sK0(X0_47),u1_struct_0(X1_47)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1730,c_825])).

cnf(c_2050,plain,
    ( m1_subset_1(sK0(X0_47),u1_struct_0(X1_47)) = iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2049])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_783,plain,
    ( ~ m1_subset_1(X0_45,X0_46)
    | v1_xboole_0(X0_46)
    | k6_domain_1(X0_46,X0_45) = k1_tarski(X0_45) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1206,plain,
    ( k6_domain_1(X0_46,X0_45) = k1_tarski(X0_45)
    | m1_subset_1(X0_45,X0_46) != iProver_top
    | v1_xboole_0(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_2063,plain,
    ( k6_domain_1(u1_struct_0(X0_47),sK0(X1_47)) = k1_tarski(sK0(X1_47))
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | v7_struct_0(X1_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_1206])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_332,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_2])).

cnf(c_768,plain,
    ( v2_struct_0(X0_47)
    | ~ v1_xboole_0(u1_struct_0(X0_47))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_332])).

cnf(c_860,plain,
    ( v2_struct_0(X0_47) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_5336,plain,
    ( v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v7_struct_0(X1_47) != iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | k6_domain_1(u1_struct_0(X0_47),sK0(X1_47)) = k1_tarski(sK0(X1_47))
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_860])).

cnf(c_5337,plain,
    ( k6_domain_1(u1_struct_0(X0_47),sK0(X1_47)) = k1_tarski(sK0(X1_47))
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | v7_struct_0(X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_5336])).

cnf(c_5348,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = k1_tarski(sK0(sK2))
    | v7_struct_0(sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_5337])).

cnf(c_16,negated_conjecture,
    ( v7_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_775,negated_conjecture,
    ( v7_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1214,plain,
    ( v7_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_1731,plain,
    ( k6_domain_1(u1_struct_0(X0_47),sK0(X0_47)) = k1_tarski(sK0(X0_47))
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1206])).

cnf(c_2035,plain,
    ( v2_struct_0(X0_47) = iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | k6_domain_1(u1_struct_0(X0_47),sK0(X0_47)) = k1_tarski(sK0(X0_47))
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1731,c_860])).

cnf(c_2036,plain,
    ( k6_domain_1(u1_struct_0(X0_47),sK0(X0_47)) = k1_tarski(sK0(X0_47))
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2035])).

cnf(c_2045,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = k1_tarski(sK0(sK2))
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_2036])).

cnf(c_7,plain,
    ( ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),sK0(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_315,plain,
    ( ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),sK0(X0)) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_0,c_7])).

cnf(c_769,plain,
    ( ~ v7_struct_0(X0_47)
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | k6_domain_1(u1_struct_0(X0_47),sK0(X0_47)) = u1_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_315])).

cnf(c_1220,plain,
    ( k6_domain_1(u1_struct_0(X0_47),sK0(X0_47)) = u1_struct_0(X0_47)
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_769])).

cnf(c_1907,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1220])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_23,plain,
    ( v7_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1412,plain,
    ( ~ v7_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_1413,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2)
    | v7_struct_0(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1412])).

cnf(c_1204,plain,
    ( m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_1439,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_1204])).

cnf(c_1910,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1907,c_21,c_22,c_23,c_1413,c_1439])).

cnf(c_2046,plain,
    ( k1_tarski(sK0(sK2)) = u1_struct_0(sK2)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2045,c_1910])).

cnf(c_2208,plain,
    ( k1_tarski(sK0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2046,c_21,c_22,c_1439])).

cnf(c_5367,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2)
    | v7_struct_0(sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5348,c_2208])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_59,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_61,plain,
    ( v2_struct_0(sK1) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_63,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_65,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_2062,plain,
    ( m1_subset_1(sK0(X0_47),u1_struct_0(X1_47)) = iProver_top
    | m1_pre_topc(X2_47,X1_47) != iProver_top
    | m1_pre_topc(X0_47,X2_47) != iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X2_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | l1_pre_topc(X2_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_1205])).

cnf(c_4364,plain,
    ( m1_subset_1(sK0(X0_47),u1_struct_0(X1_47)) = iProver_top
    | m1_pre_topc(X0_47,X2_47) != iProver_top
    | m1_pre_topc(X2_47,X1_47) != iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X2_47) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2062,c_1204])).

cnf(c_4366,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(X0_47)) = iProver_top
    | m1_pre_topc(sK1,X0_47) != iProver_top
    | v7_struct_0(sK2) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_4364])).

cnf(c_4407,plain,
    ( m1_pre_topc(sK1,X0_47) != iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(X0_47)) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4366,c_20,c_22,c_23])).

cnf(c_4408,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(X0_47)) = iProver_top
    | m1_pre_topc(sK1,X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_4407])).

cnf(c_4424,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(X0_47)) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | m1_pre_topc(sK1,X1_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_4408,c_1205])).

cnf(c_5018,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(X0_47)) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | m1_pre_topc(sK1,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4424,c_1204])).

cnf(c_5020,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_5018])).

cnf(c_24,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_465,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_298,c_16])).

cnf(c_466,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_467,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_1425,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_1498,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK2),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1425])).

cnf(c_1499,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1498])).

cnf(c_5049,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5020,c_20,c_21,c_22,c_24,c_467,c_1439,c_1499])).

cnf(c_5059,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = k1_tarski(sK0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5049,c_1206])).

cnf(c_5062,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5059,c_2208])).

cnf(c_5644,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5367,c_20,c_21,c_61,c_65,c_5062])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_pre_topc(k1_tex_2(X1,X0),X1)
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_116,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_13,c_12,c_11])).

cnf(c_117,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_116])).

cnf(c_771,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | k6_domain_1(u1_struct_0(X0_47),X0_45) = u1_struct_0(k1_tex_2(X0_47,X0_45)) ),
    inference(subtyping,[status(esa)],[c_117])).

cnf(c_1218,plain,
    ( k6_domain_1(u1_struct_0(X0_47),X0_45) = u1_struct_0(k1_tex_2(X0_47,X0_45))
    | m1_subset_1(X0_45,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_5054,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(k1_tex_2(sK1,sK0(sK2)))
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5049,c_1218])).

cnf(c_1440,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1439])).

cnf(c_1558,plain,
    ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(k1_tex_2(sK1,sK0(sK2))) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_5541,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(k1_tex_2(sK1,sK0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5054,c_19,c_18,c_17,c_15,c_466,c_1440,c_1498,c_1558])).

cnf(c_5647,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK0(sK2))) = u1_struct_0(sK2) ),
    inference(demodulation,[status(thm)],[c_5644,c_5541])).

cnf(c_794,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1620,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) != X0_48
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_48
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1817,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2))))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(X2) != u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_782,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ m1_pre_topc(X2_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | g1_pre_topc(u1_struct_0(X2_47),u1_pre_topc(X2_47)) = g1_pre_topc(u1_struct_0(X0_47),u1_pre_topc(X0_47))
    | u1_struct_0(X2_47) != u1_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1430,plain,
    ( ~ m1_pre_topc(X0_47,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(X0_47),u1_pre_topc(X0_47)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(X0_47) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_1644,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(k1_tex_2(sK1,sK0(sK2))) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1430])).

cnf(c_788,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1585,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_14,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X0)),u1_pre_topc(k1_tex_2(sK1,X0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_777,negated_conjecture,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X0_45)),u1_pre_topc(k1_tex_2(sK1,X0_45))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1573,plain,
    ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_780,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_47))
    | m1_pre_topc(k1_tex_2(X0_47,X0_45),X0_47)
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1560,plain,
    ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_1461,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1430])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5647,c_1817,c_1644,c_1585,c_1573,c_1560,c_1498,c_1461,c_1440,c_466,c_15,c_17,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.44/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/1.00  
% 2.44/1.00  ------  iProver source info
% 2.44/1.00  
% 2.44/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.44/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/1.00  git: non_committed_changes: false
% 2.44/1.00  git: last_make_outside_of_git: false
% 2.44/1.00  
% 2.44/1.00  ------ 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options
% 2.44/1.00  
% 2.44/1.00  --out_options                           all
% 2.44/1.00  --tptp_safe_out                         true
% 2.44/1.00  --problem_path                          ""
% 2.44/1.00  --include_path                          ""
% 2.44/1.00  --clausifier                            res/vclausify_rel
% 2.44/1.00  --clausifier_options                    --mode clausify
% 2.44/1.00  --stdin                                 false
% 2.44/1.00  --stats_out                             all
% 2.44/1.00  
% 2.44/1.00  ------ General Options
% 2.44/1.00  
% 2.44/1.00  --fof                                   false
% 2.44/1.00  --time_out_real                         305.
% 2.44/1.00  --time_out_virtual                      -1.
% 2.44/1.00  --symbol_type_check                     false
% 2.44/1.00  --clausify_out                          false
% 2.44/1.00  --sig_cnt_out                           false
% 2.44/1.00  --trig_cnt_out                          false
% 2.44/1.00  --trig_cnt_out_tolerance                1.
% 2.44/1.00  --trig_cnt_out_sk_spl                   false
% 2.44/1.00  --abstr_cl_out                          false
% 2.44/1.00  
% 2.44/1.00  ------ Global Options
% 2.44/1.00  
% 2.44/1.00  --schedule                              default
% 2.44/1.00  --add_important_lit                     false
% 2.44/1.00  --prop_solver_per_cl                    1000
% 2.44/1.00  --min_unsat_core                        false
% 2.44/1.00  --soft_assumptions                      false
% 2.44/1.00  --soft_lemma_size                       3
% 2.44/1.00  --prop_impl_unit_size                   0
% 2.44/1.00  --prop_impl_unit                        []
% 2.44/1.00  --share_sel_clauses                     true
% 2.44/1.00  --reset_solvers                         false
% 2.44/1.00  --bc_imp_inh                            [conj_cone]
% 2.44/1.00  --conj_cone_tolerance                   3.
% 2.44/1.00  --extra_neg_conj                        none
% 2.44/1.00  --large_theory_mode                     true
% 2.44/1.00  --prolific_symb_bound                   200
% 2.44/1.00  --lt_threshold                          2000
% 2.44/1.00  --clause_weak_htbl                      true
% 2.44/1.00  --gc_record_bc_elim                     false
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing Options
% 2.44/1.00  
% 2.44/1.00  --preprocessing_flag                    true
% 2.44/1.00  --time_out_prep_mult                    0.1
% 2.44/1.00  --splitting_mode                        input
% 2.44/1.00  --splitting_grd                         true
% 2.44/1.00  --splitting_cvd                         false
% 2.44/1.00  --splitting_cvd_svl                     false
% 2.44/1.00  --splitting_nvd                         32
% 2.44/1.00  --sub_typing                            true
% 2.44/1.00  --prep_gs_sim                           true
% 2.44/1.00  --prep_unflatten                        true
% 2.44/1.00  --prep_res_sim                          true
% 2.44/1.00  --prep_upred                            true
% 2.44/1.00  --prep_sem_filter                       exhaustive
% 2.44/1.00  --prep_sem_filter_out                   false
% 2.44/1.00  --pred_elim                             true
% 2.44/1.00  --res_sim_input                         true
% 2.44/1.00  --eq_ax_congr_red                       true
% 2.44/1.00  --pure_diseq_elim                       true
% 2.44/1.00  --brand_transform                       false
% 2.44/1.00  --non_eq_to_eq                          false
% 2.44/1.00  --prep_def_merge                        true
% 2.44/1.00  --prep_def_merge_prop_impl              false
% 2.44/1.00  --prep_def_merge_mbd                    true
% 2.44/1.00  --prep_def_merge_tr_red                 false
% 2.44/1.00  --prep_def_merge_tr_cl                  false
% 2.44/1.00  --smt_preprocessing                     true
% 2.44/1.00  --smt_ac_axioms                         fast
% 2.44/1.00  --preprocessed_out                      false
% 2.44/1.00  --preprocessed_stats                    false
% 2.44/1.00  
% 2.44/1.00  ------ Abstraction refinement Options
% 2.44/1.00  
% 2.44/1.00  --abstr_ref                             []
% 2.44/1.00  --abstr_ref_prep                        false
% 2.44/1.00  --abstr_ref_until_sat                   false
% 2.44/1.00  --abstr_ref_sig_restrict                funpre
% 2.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.00  --abstr_ref_under                       []
% 2.44/1.00  
% 2.44/1.00  ------ SAT Options
% 2.44/1.00  
% 2.44/1.00  --sat_mode                              false
% 2.44/1.00  --sat_fm_restart_options                ""
% 2.44/1.00  --sat_gr_def                            false
% 2.44/1.00  --sat_epr_types                         true
% 2.44/1.00  --sat_non_cyclic_types                  false
% 2.44/1.00  --sat_finite_models                     false
% 2.44/1.00  --sat_fm_lemmas                         false
% 2.44/1.00  --sat_fm_prep                           false
% 2.44/1.00  --sat_fm_uc_incr                        true
% 2.44/1.00  --sat_out_model                         small
% 2.44/1.00  --sat_out_clauses                       false
% 2.44/1.00  
% 2.44/1.00  ------ QBF Options
% 2.44/1.00  
% 2.44/1.00  --qbf_mode                              false
% 2.44/1.00  --qbf_elim_univ                         false
% 2.44/1.00  --qbf_dom_inst                          none
% 2.44/1.00  --qbf_dom_pre_inst                      false
% 2.44/1.00  --qbf_sk_in                             false
% 2.44/1.00  --qbf_pred_elim                         true
% 2.44/1.00  --qbf_split                             512
% 2.44/1.00  
% 2.44/1.00  ------ BMC1 Options
% 2.44/1.00  
% 2.44/1.00  --bmc1_incremental                      false
% 2.44/1.00  --bmc1_axioms                           reachable_all
% 2.44/1.00  --bmc1_min_bound                        0
% 2.44/1.00  --bmc1_max_bound                        -1
% 2.44/1.00  --bmc1_max_bound_default                -1
% 2.44/1.00  --bmc1_symbol_reachability              true
% 2.44/1.00  --bmc1_property_lemmas                  false
% 2.44/1.00  --bmc1_k_induction                      false
% 2.44/1.00  --bmc1_non_equiv_states                 false
% 2.44/1.00  --bmc1_deadlock                         false
% 2.44/1.00  --bmc1_ucm                              false
% 2.44/1.00  --bmc1_add_unsat_core                   none
% 2.44/1.00  --bmc1_unsat_core_children              false
% 2.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.00  --bmc1_out_stat                         full
% 2.44/1.00  --bmc1_ground_init                      false
% 2.44/1.00  --bmc1_pre_inst_next_state              false
% 2.44/1.00  --bmc1_pre_inst_state                   false
% 2.44/1.00  --bmc1_pre_inst_reach_state             false
% 2.44/1.00  --bmc1_out_unsat_core                   false
% 2.44/1.00  --bmc1_aig_witness_out                  false
% 2.44/1.00  --bmc1_verbose                          false
% 2.44/1.00  --bmc1_dump_clauses_tptp                false
% 2.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.00  --bmc1_dump_file                        -
% 2.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.00  --bmc1_ucm_extend_mode                  1
% 2.44/1.00  --bmc1_ucm_init_mode                    2
% 2.44/1.00  --bmc1_ucm_cone_mode                    none
% 2.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.00  --bmc1_ucm_relax_model                  4
% 2.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.00  --bmc1_ucm_layered_model                none
% 2.44/1.00  --bmc1_ucm_max_lemma_size               10
% 2.44/1.00  
% 2.44/1.00  ------ AIG Options
% 2.44/1.00  
% 2.44/1.00  --aig_mode                              false
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation Options
% 2.44/1.00  
% 2.44/1.00  --instantiation_flag                    true
% 2.44/1.00  --inst_sos_flag                         false
% 2.44/1.00  --inst_sos_phase                        true
% 2.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel_side                     num_symb
% 2.44/1.00  --inst_solver_per_active                1400
% 2.44/1.00  --inst_solver_calls_frac                1.
% 2.44/1.00  --inst_passive_queue_type               priority_queues
% 2.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.00  --inst_passive_queues_freq              [25;2]
% 2.44/1.00  --inst_dismatching                      true
% 2.44/1.00  --inst_eager_unprocessed_to_passive     true
% 2.44/1.00  --inst_prop_sim_given                   true
% 2.44/1.00  --inst_prop_sim_new                     false
% 2.44/1.00  --inst_subs_new                         false
% 2.44/1.00  --inst_eq_res_simp                      false
% 2.44/1.00  --inst_subs_given                       false
% 2.44/1.00  --inst_orphan_elimination               true
% 2.44/1.00  --inst_learning_loop_flag               true
% 2.44/1.00  --inst_learning_start                   3000
% 2.44/1.00  --inst_learning_factor                  2
% 2.44/1.00  --inst_start_prop_sim_after_learn       3
% 2.44/1.00  --inst_sel_renew                        solver
% 2.44/1.00  --inst_lit_activity_flag                true
% 2.44/1.00  --inst_restr_to_given                   false
% 2.44/1.00  --inst_activity_threshold               500
% 2.44/1.00  --inst_out_proof                        true
% 2.44/1.00  
% 2.44/1.00  ------ Resolution Options
% 2.44/1.00  
% 2.44/1.00  --resolution_flag                       true
% 2.44/1.00  --res_lit_sel                           adaptive
% 2.44/1.00  --res_lit_sel_side                      none
% 2.44/1.00  --res_ordering                          kbo
% 2.44/1.00  --res_to_prop_solver                    active
% 2.44/1.00  --res_prop_simpl_new                    false
% 2.44/1.00  --res_prop_simpl_given                  true
% 2.44/1.00  --res_passive_queue_type                priority_queues
% 2.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.00  --res_passive_queues_freq               [15;5]
% 2.44/1.00  --res_forward_subs                      full
% 2.44/1.00  --res_backward_subs                     full
% 2.44/1.00  --res_forward_subs_resolution           true
% 2.44/1.00  --res_backward_subs_resolution          true
% 2.44/1.00  --res_orphan_elimination                true
% 2.44/1.00  --res_time_limit                        2.
% 2.44/1.00  --res_out_proof                         true
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Options
% 2.44/1.00  
% 2.44/1.00  --superposition_flag                    true
% 2.44/1.00  --sup_passive_queue_type                priority_queues
% 2.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.00  --demod_completeness_check              fast
% 2.44/1.00  --demod_use_ground                      true
% 2.44/1.00  --sup_to_prop_solver                    passive
% 2.44/1.00  --sup_prop_simpl_new                    true
% 2.44/1.00  --sup_prop_simpl_given                  true
% 2.44/1.00  --sup_fun_splitting                     false
% 2.44/1.00  --sup_smt_interval                      50000
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Simplification Setup
% 2.44/1.00  
% 2.44/1.00  --sup_indices_passive                   []
% 2.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_full_bw                           [BwDemod]
% 2.44/1.00  --sup_immed_triv                        [TrivRules]
% 2.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_immed_bw_main                     []
% 2.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  
% 2.44/1.00  ------ Combination Options
% 2.44/1.00  
% 2.44/1.00  --comb_res_mult                         3
% 2.44/1.00  --comb_sup_mult                         2
% 2.44/1.00  --comb_inst_mult                        10
% 2.44/1.00  
% 2.44/1.00  ------ Debug Options
% 2.44/1.00  
% 2.44/1.00  --dbg_backtrace                         false
% 2.44/1.00  --dbg_dump_prop_clauses                 false
% 2.44/1.00  --dbg_dump_prop_clauses_file            -
% 2.44/1.00  --dbg_out_stat                          false
% 2.44/1.00  ------ Parsing...
% 2.44/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/1.00  ------ Proving...
% 2.44/1.00  ------ Problem Properties 
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  clauses                                 19
% 2.44/1.00  conjectures                             6
% 2.44/1.00  EPR                                     6
% 2.44/1.00  Horn                                    10
% 2.44/1.00  unary                                   5
% 2.44/1.00  binary                                  1
% 2.44/1.00  lits                                    64
% 2.44/1.00  lits eq                                 9
% 2.44/1.00  fd_pure                                 0
% 2.44/1.00  fd_pseudo                               0
% 2.44/1.00  fd_cond                                 0
% 2.44/1.00  fd_pseudo_cond                          1
% 2.44/1.00  AC symbols                              0
% 2.44/1.00  
% 2.44/1.00  ------ Schedule dynamic 5 is on 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  ------ 
% 2.44/1.00  Current options:
% 2.44/1.00  ------ 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options
% 2.44/1.00  
% 2.44/1.00  --out_options                           all
% 2.44/1.00  --tptp_safe_out                         true
% 2.44/1.00  --problem_path                          ""
% 2.44/1.00  --include_path                          ""
% 2.44/1.00  --clausifier                            res/vclausify_rel
% 2.44/1.00  --clausifier_options                    --mode clausify
% 2.44/1.00  --stdin                                 false
% 2.44/1.00  --stats_out                             all
% 2.44/1.00  
% 2.44/1.00  ------ General Options
% 2.44/1.00  
% 2.44/1.00  --fof                                   false
% 2.44/1.00  --time_out_real                         305.
% 2.44/1.00  --time_out_virtual                      -1.
% 2.44/1.00  --symbol_type_check                     false
% 2.44/1.00  --clausify_out                          false
% 2.44/1.00  --sig_cnt_out                           false
% 2.44/1.00  --trig_cnt_out                          false
% 2.44/1.00  --trig_cnt_out_tolerance                1.
% 2.44/1.00  --trig_cnt_out_sk_spl                   false
% 2.44/1.00  --abstr_cl_out                          false
% 2.44/1.00  
% 2.44/1.00  ------ Global Options
% 2.44/1.00  
% 2.44/1.00  --schedule                              default
% 2.44/1.00  --add_important_lit                     false
% 2.44/1.00  --prop_solver_per_cl                    1000
% 2.44/1.00  --min_unsat_core                        false
% 2.44/1.00  --soft_assumptions                      false
% 2.44/1.00  --soft_lemma_size                       3
% 2.44/1.00  --prop_impl_unit_size                   0
% 2.44/1.00  --prop_impl_unit                        []
% 2.44/1.00  --share_sel_clauses                     true
% 2.44/1.00  --reset_solvers                         false
% 2.44/1.00  --bc_imp_inh                            [conj_cone]
% 2.44/1.00  --conj_cone_tolerance                   3.
% 2.44/1.00  --extra_neg_conj                        none
% 2.44/1.00  --large_theory_mode                     true
% 2.44/1.00  --prolific_symb_bound                   200
% 2.44/1.00  --lt_threshold                          2000
% 2.44/1.00  --clause_weak_htbl                      true
% 2.44/1.00  --gc_record_bc_elim                     false
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing Options
% 2.44/1.00  
% 2.44/1.00  --preprocessing_flag                    true
% 2.44/1.00  --time_out_prep_mult                    0.1
% 2.44/1.00  --splitting_mode                        input
% 2.44/1.00  --splitting_grd                         true
% 2.44/1.00  --splitting_cvd                         false
% 2.44/1.00  --splitting_cvd_svl                     false
% 2.44/1.00  --splitting_nvd                         32
% 2.44/1.00  --sub_typing                            true
% 2.44/1.00  --prep_gs_sim                           true
% 2.44/1.00  --prep_unflatten                        true
% 2.44/1.00  --prep_res_sim                          true
% 2.44/1.00  --prep_upred                            true
% 2.44/1.00  --prep_sem_filter                       exhaustive
% 2.44/1.00  --prep_sem_filter_out                   false
% 2.44/1.00  --pred_elim                             true
% 2.44/1.00  --res_sim_input                         true
% 2.44/1.00  --eq_ax_congr_red                       true
% 2.44/1.00  --pure_diseq_elim                       true
% 2.44/1.00  --brand_transform                       false
% 2.44/1.00  --non_eq_to_eq                          false
% 2.44/1.00  --prep_def_merge                        true
% 2.44/1.00  --prep_def_merge_prop_impl              false
% 2.44/1.00  --prep_def_merge_mbd                    true
% 2.44/1.00  --prep_def_merge_tr_red                 false
% 2.44/1.00  --prep_def_merge_tr_cl                  false
% 2.44/1.00  --smt_preprocessing                     true
% 2.44/1.00  --smt_ac_axioms                         fast
% 2.44/1.00  --preprocessed_out                      false
% 2.44/1.00  --preprocessed_stats                    false
% 2.44/1.00  
% 2.44/1.00  ------ Abstraction refinement Options
% 2.44/1.00  
% 2.44/1.00  --abstr_ref                             []
% 2.44/1.00  --abstr_ref_prep                        false
% 2.44/1.00  --abstr_ref_until_sat                   false
% 2.44/1.00  --abstr_ref_sig_restrict                funpre
% 2.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.00  --abstr_ref_under                       []
% 2.44/1.00  
% 2.44/1.00  ------ SAT Options
% 2.44/1.00  
% 2.44/1.00  --sat_mode                              false
% 2.44/1.00  --sat_fm_restart_options                ""
% 2.44/1.00  --sat_gr_def                            false
% 2.44/1.00  --sat_epr_types                         true
% 2.44/1.00  --sat_non_cyclic_types                  false
% 2.44/1.00  --sat_finite_models                     false
% 2.44/1.00  --sat_fm_lemmas                         false
% 2.44/1.00  --sat_fm_prep                           false
% 2.44/1.00  --sat_fm_uc_incr                        true
% 2.44/1.00  --sat_out_model                         small
% 2.44/1.00  --sat_out_clauses                       false
% 2.44/1.00  
% 2.44/1.00  ------ QBF Options
% 2.44/1.00  
% 2.44/1.00  --qbf_mode                              false
% 2.44/1.00  --qbf_elim_univ                         false
% 2.44/1.00  --qbf_dom_inst                          none
% 2.44/1.00  --qbf_dom_pre_inst                      false
% 2.44/1.00  --qbf_sk_in                             false
% 2.44/1.00  --qbf_pred_elim                         true
% 2.44/1.00  --qbf_split                             512
% 2.44/1.00  
% 2.44/1.00  ------ BMC1 Options
% 2.44/1.00  
% 2.44/1.00  --bmc1_incremental                      false
% 2.44/1.00  --bmc1_axioms                           reachable_all
% 2.44/1.00  --bmc1_min_bound                        0
% 2.44/1.00  --bmc1_max_bound                        -1
% 2.44/1.00  --bmc1_max_bound_default                -1
% 2.44/1.00  --bmc1_symbol_reachability              true
% 2.44/1.00  --bmc1_property_lemmas                  false
% 2.44/1.00  --bmc1_k_induction                      false
% 2.44/1.00  --bmc1_non_equiv_states                 false
% 2.44/1.00  --bmc1_deadlock                         false
% 2.44/1.00  --bmc1_ucm                              false
% 2.44/1.00  --bmc1_add_unsat_core                   none
% 2.44/1.00  --bmc1_unsat_core_children              false
% 2.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.00  --bmc1_out_stat                         full
% 2.44/1.00  --bmc1_ground_init                      false
% 2.44/1.00  --bmc1_pre_inst_next_state              false
% 2.44/1.00  --bmc1_pre_inst_state                   false
% 2.44/1.00  --bmc1_pre_inst_reach_state             false
% 2.44/1.00  --bmc1_out_unsat_core                   false
% 2.44/1.00  --bmc1_aig_witness_out                  false
% 2.44/1.00  --bmc1_verbose                          false
% 2.44/1.00  --bmc1_dump_clauses_tptp                false
% 2.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.00  --bmc1_dump_file                        -
% 2.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.00  --bmc1_ucm_extend_mode                  1
% 2.44/1.00  --bmc1_ucm_init_mode                    2
% 2.44/1.00  --bmc1_ucm_cone_mode                    none
% 2.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.00  --bmc1_ucm_relax_model                  4
% 2.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.00  --bmc1_ucm_layered_model                none
% 2.44/1.00  --bmc1_ucm_max_lemma_size               10
% 2.44/1.00  
% 2.44/1.00  ------ AIG Options
% 2.44/1.00  
% 2.44/1.00  --aig_mode                              false
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation Options
% 2.44/1.00  
% 2.44/1.00  --instantiation_flag                    true
% 2.44/1.00  --inst_sos_flag                         false
% 2.44/1.00  --inst_sos_phase                        true
% 2.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel_side                     none
% 2.44/1.00  --inst_solver_per_active                1400
% 2.44/1.00  --inst_solver_calls_frac                1.
% 2.44/1.00  --inst_passive_queue_type               priority_queues
% 2.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.00  --inst_passive_queues_freq              [25;2]
% 2.44/1.00  --inst_dismatching                      true
% 2.44/1.00  --inst_eager_unprocessed_to_passive     true
% 2.44/1.00  --inst_prop_sim_given                   true
% 2.44/1.00  --inst_prop_sim_new                     false
% 2.44/1.00  --inst_subs_new                         false
% 2.44/1.00  --inst_eq_res_simp                      false
% 2.44/1.00  --inst_subs_given                       false
% 2.44/1.00  --inst_orphan_elimination               true
% 2.44/1.00  --inst_learning_loop_flag               true
% 2.44/1.00  --inst_learning_start                   3000
% 2.44/1.00  --inst_learning_factor                  2
% 2.44/1.00  --inst_start_prop_sim_after_learn       3
% 2.44/1.00  --inst_sel_renew                        solver
% 2.44/1.00  --inst_lit_activity_flag                true
% 2.44/1.00  --inst_restr_to_given                   false
% 2.44/1.00  --inst_activity_threshold               500
% 2.44/1.00  --inst_out_proof                        true
% 2.44/1.00  
% 2.44/1.00  ------ Resolution Options
% 2.44/1.00  
% 2.44/1.00  --resolution_flag                       false
% 2.44/1.00  --res_lit_sel                           adaptive
% 2.44/1.00  --res_lit_sel_side                      none
% 2.44/1.00  --res_ordering                          kbo
% 2.44/1.00  --res_to_prop_solver                    active
% 2.44/1.00  --res_prop_simpl_new                    false
% 2.44/1.00  --res_prop_simpl_given                  true
% 2.44/1.00  --res_passive_queue_type                priority_queues
% 2.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.00  --res_passive_queues_freq               [15;5]
% 2.44/1.00  --res_forward_subs                      full
% 2.44/1.00  --res_backward_subs                     full
% 2.44/1.00  --res_forward_subs_resolution           true
% 2.44/1.00  --res_backward_subs_resolution          true
% 2.44/1.00  --res_orphan_elimination                true
% 2.44/1.00  --res_time_limit                        2.
% 2.44/1.00  --res_out_proof                         true
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Options
% 2.44/1.00  
% 2.44/1.00  --superposition_flag                    true
% 2.44/1.00  --sup_passive_queue_type                priority_queues
% 2.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.00  --demod_completeness_check              fast
% 2.44/1.00  --demod_use_ground                      true
% 2.44/1.00  --sup_to_prop_solver                    passive
% 2.44/1.00  --sup_prop_simpl_new                    true
% 2.44/1.00  --sup_prop_simpl_given                  true
% 2.44/1.00  --sup_fun_splitting                     false
% 2.44/1.00  --sup_smt_interval                      50000
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Simplification Setup
% 2.44/1.00  
% 2.44/1.00  --sup_indices_passive                   []
% 2.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_full_bw                           [BwDemod]
% 2.44/1.00  --sup_immed_triv                        [TrivRules]
% 2.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_immed_bw_main                     []
% 2.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  
% 2.44/1.00  ------ Combination Options
% 2.44/1.00  
% 2.44/1.00  --comb_res_mult                         3
% 2.44/1.00  --comb_sup_mult                         2
% 2.44/1.00  --comb_inst_mult                        10
% 2.44/1.00  
% 2.44/1.00  ------ Debug Options
% 2.44/1.00  
% 2.44/1.00  --dbg_backtrace                         false
% 2.44/1.00  --dbg_dump_prop_clauses                 false
% 2.44/1.00  --dbg_dump_prop_clauses_file            -
% 2.44/1.00  --dbg_out_stat                          false
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  ------ Proving...
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS status Theorem for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  fof(f10,conjecture,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f11,negated_conjecture,(
% 2.44/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.44/1.00    inference(negated_conjecture,[],[f10])).
% 2.44/1.00  
% 2.44/1.00  fof(f28,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & (m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f11])).
% 2.44/1.00  
% 2.44/1.00  fof(f29,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f28])).
% 2.44/1.00  
% 2.44/1.00  fof(f36,plain,(
% 2.44/1.00    ( ! [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (! [X2] : (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(sK2,X0) & v7_struct_0(sK2) & ~v2_struct_0(sK2))) )),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f35,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2))) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_pre_topc(X1,sK1) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f37,plain,(
% 2.44/1.00    (! [X2] : (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2))) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_pre_topc(sK2,sK1) & v7_struct_0(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f36,f35])).
% 2.44/1.00  
% 2.44/1.00  fof(f56,plain,(
% 2.44/1.00    m1_pre_topc(sK2,sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f1,axiom,(
% 2.44/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f12,plain,(
% 2.44/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.44/1.00    inference(ennf_transformation,[],[f1])).
% 2.44/1.00  
% 2.44/1.00  fof(f38,plain,(
% 2.44/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f12])).
% 2.44/1.00  
% 2.44/1.00  fof(f7,axiom,(
% 2.44/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f22,plain,(
% 2.44/1.00    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f7])).
% 2.44/1.00  
% 2.44/1.00  fof(f23,plain,(
% 2.44/1.00    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f22])).
% 2.44/1.00  
% 2.44/1.00  fof(f30,plain,(
% 2.44/1.00    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(nnf_transformation,[],[f23])).
% 2.44/1.00  
% 2.44/1.00  fof(f31,plain,(
% 2.44/1.00    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(rectify,[],[f30])).
% 2.44/1.00  
% 2.44/1.00  fof(f32,plain,(
% 2.44/1.00    ! [X0] : (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0)) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f33,plain,(
% 2.44/1.00    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0)) & m1_subset_1(sK0(X0),u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.44/1.00  
% 2.44/1.00  fof(f44,plain,(
% 2.44/1.00    ( ! [X0] : (m1_subset_1(sK0(X0),u1_struct_0(X0)) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f33])).
% 2.44/1.00  
% 2.44/1.00  fof(f4,axiom,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f16,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f4])).
% 2.44/1.00  
% 2.44/1.00  fof(f17,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f16])).
% 2.44/1.00  
% 2.44/1.00  fof(f41,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f17])).
% 2.44/1.00  
% 2.44/1.00  fof(f2,axiom,(
% 2.44/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f13,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.44/1.00    inference(ennf_transformation,[],[f2])).
% 2.44/1.00  
% 2.44/1.00  fof(f39,plain,(
% 2.44/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f13])).
% 2.44/1.00  
% 2.44/1.00  fof(f5,axiom,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f18,plain,(
% 2.44/1.00    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f5])).
% 2.44/1.00  
% 2.44/1.00  fof(f19,plain,(
% 2.44/1.00    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.44/1.00    inference(flattening,[],[f18])).
% 2.44/1.00  
% 2.44/1.00  fof(f42,plain,(
% 2.44/1.00    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f19])).
% 2.44/1.00  
% 2.44/1.00  fof(f3,axiom,(
% 2.44/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f14,plain,(
% 2.44/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f3])).
% 2.44/1.00  
% 2.44/1.00  fof(f15,plain,(
% 2.44/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f14])).
% 2.44/1.00  
% 2.44/1.00  fof(f40,plain,(
% 2.44/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f15])).
% 2.44/1.00  
% 2.44/1.00  fof(f55,plain,(
% 2.44/1.00    v7_struct_0(sK2)),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f45,plain,(
% 2.44/1.00    ( ! [X0] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0)) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f33])).
% 2.44/1.00  
% 2.44/1.00  fof(f53,plain,(
% 2.44/1.00    l1_pre_topc(sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f54,plain,(
% 2.44/1.00    ~v2_struct_0(sK2)),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f52,plain,(
% 2.44/1.00    ~v2_struct_0(sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f8,axiom,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f24,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f8])).
% 2.44/1.00  
% 2.44/1.00  fof(f25,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f24])).
% 2.44/1.00  
% 2.44/1.00  fof(f34,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(nnf_transformation,[],[f25])).
% 2.44/1.00  
% 2.44/1.00  fof(f47,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f34])).
% 2.44/1.00  
% 2.44/1.00  fof(f58,plain,(
% 2.44/1.00    ( ! [X0,X1] : (u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(equality_resolution,[],[f47])).
% 2.44/1.00  
% 2.44/1.00  fof(f9,axiom,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f26,plain,(
% 2.44/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f9])).
% 2.44/1.00  
% 2.44/1.00  fof(f27,plain,(
% 2.44/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f26])).
% 2.44/1.00  
% 2.44/1.00  fof(f49,plain,(
% 2.44/1.00    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f27])).
% 2.44/1.00  
% 2.44/1.00  fof(f50,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f27])).
% 2.44/1.00  
% 2.44/1.00  fof(f51,plain,(
% 2.44/1.00    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f27])).
% 2.44/1.00  
% 2.44/1.00  fof(f6,axiom,(
% 2.44/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (u1_struct_0(X1) = u1_struct_0(X2) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f20,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.44/1.00    inference(ennf_transformation,[],[f6])).
% 2.44/1.00  
% 2.44/1.00  fof(f21,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.44/1.00    inference(flattening,[],[f20])).
% 2.44/1.00  
% 2.44/1.00  fof(f43,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f21])).
% 2.44/1.00  
% 2.44/1.00  fof(f57,plain,(
% 2.44/1.00    ( ! [X2] : (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2))) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  cnf(c_15,negated_conjecture,
% 2.44/1.00      ( m1_pre_topc(sK2,sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_776,negated_conjecture,
% 2.44/1.00      ( m1_pre_topc(sK2,sK1) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1213,plain,
% 2.44/1.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_776]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_0,plain,
% 2.44/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_8,plain,
% 2.44/1.00      ( m1_subset_1(sK0(X0),u1_struct_0(X0))
% 2.44/1.00      | ~ v7_struct_0(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_struct_0(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_298,plain,
% 2.44/1.00      ( m1_subset_1(sK0(X0),u1_struct_0(X0))
% 2.44/1.00      | ~ v7_struct_0(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(resolution,[status(thm)],[c_0,c_8]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_770,plain,
% 2.44/1.00      ( m1_subset_1(sK0(X0_47),u1_struct_0(X0_47))
% 2.44/1.00      | ~ v7_struct_0(X0_47)
% 2.44/1.00      | v2_struct_0(X0_47)
% 2.44/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_298]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1219,plain,
% 2.44/1.00      ( m1_subset_1(sK0(X0_47),u1_struct_0(X0_47)) = iProver_top
% 2.44/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.44/1.00      | m1_subset_1(X0,u1_struct_0(X2))
% 2.44/1.00      | ~ m1_pre_topc(X1,X2)
% 2.44/1.00      | v2_struct_0(X2)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X2) ),
% 2.44/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_784,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_47))
% 2.44/1.00      | m1_subset_1(X0_45,u1_struct_0(X1_47))
% 2.44/1.00      | ~ m1_pre_topc(X0_47,X1_47)
% 2.44/1.00      | v2_struct_0(X1_47)
% 2.44/1.00      | v2_struct_0(X0_47)
% 2.44/1.00      | ~ l1_pre_topc(X1_47) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1205,plain,
% 2.44/1.00      ( m1_subset_1(X0_45,u1_struct_0(X0_47)) != iProver_top
% 2.44/1.00      | m1_subset_1(X0_45,u1_struct_0(X1_47)) = iProver_top
% 2.44/1.00      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X1_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X1_47) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1730,plain,
% 2.44/1.00      ( m1_subset_1(sK0(X0_47),u1_struct_0(X1_47)) = iProver_top
% 2.44/1.00      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.44/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X1_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X1_47) != iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1219,c_1205]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_785,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.44/1.00      | ~ l1_pre_topc(X1_47)
% 2.44/1.00      | l1_pre_topc(X0_47) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_825,plain,
% 2.44/1.00      ( m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.44/1.00      | l1_pre_topc(X1_47) != iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2049,plain,
% 2.44/1.00      ( l1_pre_topc(X1_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X1_47) = iProver_top
% 2.44/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.44/1.00      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.44/1.00      | m1_subset_1(sK0(X0_47),u1_struct_0(X1_47)) = iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1730,c_825]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2050,plain,
% 2.44/1.00      ( m1_subset_1(sK0(X0_47),u1_struct_0(X1_47)) = iProver_top
% 2.44/1.00      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.44/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X1_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X1_47) != iProver_top ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_2049]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,X1)
% 2.44/1.00      | v1_xboole_0(X1)
% 2.44/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_783,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0_45,X0_46)
% 2.44/1.00      | v1_xboole_0(X0_46)
% 2.44/1.00      | k6_domain_1(X0_46,X0_45) = k1_tarski(X0_45) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1206,plain,
% 2.44/1.00      ( k6_domain_1(X0_46,X0_45) = k1_tarski(X0_45)
% 2.44/1.00      | m1_subset_1(X0_45,X0_46) != iProver_top
% 2.44/1.00      | v1_xboole_0(X0_46) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2063,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(X0_47),sK0(X1_47)) = k1_tarski(sK0(X1_47))
% 2.44/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.44/1.00      | v7_struct_0(X1_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X1_47) = iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2050,c_1206]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2,plain,
% 2.44/1.00      ( v2_struct_0(X0)
% 2.44/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.44/1.00      | ~ l1_struct_0(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_332,plain,
% 2.44/1.00      ( v2_struct_0(X0)
% 2.44/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.44/1.00      | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(resolution,[status(thm)],[c_0,c_2]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_768,plain,
% 2.44/1.00      ( v2_struct_0(X0_47)
% 2.44/1.00      | ~ v1_xboole_0(u1_struct_0(X0_47))
% 2.44/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_332]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_860,plain,
% 2.44/1.00      ( v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(X0_47)) != iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5336,plain,
% 2.44/1.00      ( v2_struct_0(X1_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | v7_struct_0(X1_47) != iProver_top
% 2.44/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.44/1.00      | k6_domain_1(u1_struct_0(X0_47),sK0(X1_47)) = k1_tarski(sK0(X1_47))
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2063,c_860]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5337,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(X0_47),sK0(X1_47)) = k1_tarski(sK0(X1_47))
% 2.44/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.44/1.00      | v7_struct_0(X1_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X1_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_5336]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5348,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = k1_tarski(sK0(sK2))
% 2.44/1.00      | v7_struct_0(sK2) != iProver_top
% 2.44/1.00      | v2_struct_0(sK1) = iProver_top
% 2.44/1.00      | v2_struct_0(sK2) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1213,c_5337]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_16,negated_conjecture,
% 2.44/1.00      ( v7_struct_0(sK2) ),
% 2.44/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_775,negated_conjecture,
% 2.44/1.00      ( v7_struct_0(sK2) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1214,plain,
% 2.44/1.00      ( v7_struct_0(sK2) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1731,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(X0_47),sK0(X0_47)) = k1_tarski(sK0(X0_47))
% 2.44/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1219,c_1206]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2035,plain,
% 2.44/1.00      ( v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.44/1.00      | k6_domain_1(u1_struct_0(X0_47),sK0(X0_47)) = k1_tarski(sK0(X0_47))
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1731,c_860]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2036,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(X0_47),sK0(X0_47)) = k1_tarski(sK0(X0_47))
% 2.44/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_2035]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2045,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = k1_tarski(sK0(sK2))
% 2.44/1.00      | v2_struct_0(sK2) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1214,c_2036]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_7,plain,
% 2.44/1.00      ( ~ v7_struct_0(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_struct_0(X0)
% 2.44/1.00      | k6_domain_1(u1_struct_0(X0),sK0(X0)) = u1_struct_0(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_315,plain,
% 2.44/1.00      ( ~ v7_struct_0(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | k6_domain_1(u1_struct_0(X0),sK0(X0)) = u1_struct_0(X0) ),
% 2.44/1.00      inference(resolution,[status(thm)],[c_0,c_7]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_769,plain,
% 2.44/1.00      ( ~ v7_struct_0(X0_47)
% 2.44/1.00      | v2_struct_0(X0_47)
% 2.44/1.00      | ~ l1_pre_topc(X0_47)
% 2.44/1.00      | k6_domain_1(u1_struct_0(X0_47),sK0(X0_47)) = u1_struct_0(X0_47) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_315]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1220,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(X0_47),sK0(X0_47)) = u1_struct_0(X0_47)
% 2.44/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_769]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1907,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2)
% 2.44/1.00      | v2_struct_0(sK2) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1214,c_1220]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_18,negated_conjecture,
% 2.44/1.00      ( l1_pre_topc(sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_21,plain,
% 2.44/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_17,negated_conjecture,
% 2.44/1.00      ( ~ v2_struct_0(sK2) ),
% 2.44/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_22,plain,
% 2.44/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_23,plain,
% 2.44/1.00      ( v7_struct_0(sK2) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1412,plain,
% 2.44/1.00      ( ~ v7_struct_0(sK2)
% 2.44/1.00      | v2_struct_0(sK2)
% 2.44/1.00      | ~ l1_pre_topc(sK2)
% 2.44/1.00      | k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_769]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1413,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2)
% 2.44/1.00      | v7_struct_0(sK2) != iProver_top
% 2.44/1.00      | v2_struct_0(sK2) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1412]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1204,plain,
% 2.44/1.00      ( m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.44/1.00      | l1_pre_topc(X1_47) != iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1439,plain,
% 2.44/1.00      ( l1_pre_topc(sK1) != iProver_top
% 2.44/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1213,c_1204]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1910,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1907,c_21,c_22,c_23,c_1413,c_1439]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2046,plain,
% 2.44/1.00      ( k1_tarski(sK0(sK2)) = u1_struct_0(sK2)
% 2.44/1.00      | v2_struct_0(sK2) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_2045,c_1910]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2208,plain,
% 2.44/1.00      ( k1_tarski(sK0(sK2)) = u1_struct_0(sK2) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2046,c_21,c_22,c_1439]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5367,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2)
% 2.44/1.00      | v7_struct_0(sK2) != iProver_top
% 2.44/1.00      | v2_struct_0(sK1) = iProver_top
% 2.44/1.00      | v2_struct_0(sK2) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_5348,c_2208]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_19,negated_conjecture,
% 2.44/1.00      ( ~ v2_struct_0(sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_20,plain,
% 2.44/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_59,plain,
% 2.44/1.00      ( v2_struct_0(X0) = iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 2.44/1.00      | l1_struct_0(X0) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_61,plain,
% 2.44/1.00      ( v2_struct_0(sK1) = iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | l1_struct_0(sK1) != iProver_top ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_59]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_63,plain,
% 2.44/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_65,plain,
% 2.44/1.00      ( l1_pre_topc(sK1) != iProver_top
% 2.44/1.00      | l1_struct_0(sK1) = iProver_top ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_63]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2062,plain,
% 2.44/1.00      ( m1_subset_1(sK0(X0_47),u1_struct_0(X1_47)) = iProver_top
% 2.44/1.00      | m1_pre_topc(X2_47,X1_47) != iProver_top
% 2.44/1.00      | m1_pre_topc(X0_47,X2_47) != iProver_top
% 2.44/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X2_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X1_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X2_47) != iProver_top
% 2.44/1.00      | l1_pre_topc(X1_47) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2050,c_1205]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4364,plain,
% 2.44/1.00      ( m1_subset_1(sK0(X0_47),u1_struct_0(X1_47)) = iProver_top
% 2.44/1.00      | m1_pre_topc(X0_47,X2_47) != iProver_top
% 2.44/1.00      | m1_pre_topc(X2_47,X1_47) != iProver_top
% 2.44/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X1_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X2_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X1_47) != iProver_top ),
% 2.44/1.00      inference(forward_subsumption_resolution,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2062,c_1204]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4366,plain,
% 2.44/1.00      ( m1_subset_1(sK0(sK2),u1_struct_0(X0_47)) = iProver_top
% 2.44/1.00      | m1_pre_topc(sK1,X0_47) != iProver_top
% 2.44/1.00      | v7_struct_0(sK2) != iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | v2_struct_0(sK1) = iProver_top
% 2.44/1.00      | v2_struct_0(sK2) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1213,c_4364]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4407,plain,
% 2.44/1.00      ( m1_pre_topc(sK1,X0_47) != iProver_top
% 2.44/1.00      | m1_subset_1(sK0(sK2),u1_struct_0(X0_47)) = iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_4366,c_20,c_22,c_23]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4408,plain,
% 2.44/1.00      ( m1_subset_1(sK0(sK2),u1_struct_0(X0_47)) = iProver_top
% 2.44/1.00      | m1_pre_topc(sK1,X0_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_4407]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4424,plain,
% 2.44/1.00      ( m1_subset_1(sK0(sK2),u1_struct_0(X0_47)) = iProver_top
% 2.44/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.44/1.00      | m1_pre_topc(sK1,X1_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X1_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top
% 2.44/1.00      | l1_pre_topc(X1_47) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_4408,c_1205]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5018,plain,
% 2.44/1.00      ( m1_subset_1(sK0(sK2),u1_struct_0(X0_47)) = iProver_top
% 2.44/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.44/1.00      | m1_pre_topc(sK1,X1_47) != iProver_top
% 2.44/1.00      | v2_struct_0(X1_47) = iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(forward_subsumption_resolution,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_4424,c_1204]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5020,plain,
% 2.44/1.00      ( m1_subset_1(sK0(sK2),u1_struct_0(sK1)) = iProver_top
% 2.44/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.44/1.00      | v2_struct_0(sK1) = iProver_top
% 2.44/1.00      | v2_struct_0(sK2) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1213,c_5018]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_24,plain,
% 2.44/1.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_465,plain,
% 2.44/1.00      ( m1_subset_1(sK0(X0),u1_struct_0(X0))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | sK2 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_298,c_16]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_466,plain,
% 2.44/1.00      ( m1_subset_1(sK0(sK2),u1_struct_0(sK2))
% 2.44/1.00      | v2_struct_0(sK2)
% 2.44/1.00      | ~ l1_pre_topc(sK2) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_465]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_467,plain,
% 2.44/1.00      ( m1_subset_1(sK0(sK2),u1_struct_0(sK2)) = iProver_top
% 2.44/1.00      | v2_struct_0(sK2) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1425,plain,
% 2.44/1.00      ( m1_subset_1(X0_45,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 2.44/1.00      | ~ m1_pre_topc(sK2,sK1)
% 2.44/1.00      | v2_struct_0(sK1)
% 2.44/1.00      | v2_struct_0(sK2)
% 2.44/1.00      | ~ l1_pre_topc(sK1) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_784]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1498,plain,
% 2.44/1.00      ( m1_subset_1(sK0(sK2),u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(sK0(sK2),u1_struct_0(sK2))
% 2.44/1.00      | ~ m1_pre_topc(sK2,sK1)
% 2.44/1.00      | v2_struct_0(sK1)
% 2.44/1.00      | v2_struct_0(sK2)
% 2.44/1.00      | ~ l1_pre_topc(sK1) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1425]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1499,plain,
% 2.44/1.00      ( m1_subset_1(sK0(sK2),u1_struct_0(sK1)) = iProver_top
% 2.44/1.00      | m1_subset_1(sK0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.44/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.44/1.00      | v2_struct_0(sK1) = iProver_top
% 2.44/1.00      | v2_struct_0(sK2) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1498]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5049,plain,
% 2.44/1.00      ( m1_subset_1(sK0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_5020,c_20,c_21,c_22,c_24,c_467,c_1439,c_1499]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5059,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = k1_tarski(sK0(sK2))
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_5049,c_1206]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5062,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2)
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_5059,c_2208]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5644,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_5367,c_20,c_21,c_61,c_65,c_5062]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_10,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.44/1.00      | ~ m1_pre_topc(k1_tex_2(X1,X0),X1)
% 2.44/1.00      | ~ v1_pre_topc(k1_tex_2(X1,X0))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | v2_struct_0(k1_tex_2(X1,X0))
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_13,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_12,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.44/1.00      | v1_pre_topc(k1_tex_2(X1,X0))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_11,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.44/1.00      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_116,plain,
% 2.44/1.00      ( v2_struct_0(X1)
% 2.44/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_10,c_13,c_12,c_11]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_117,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_116]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_771,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_47))
% 2.44/1.00      | v2_struct_0(X0_47)
% 2.44/1.00      | ~ l1_pre_topc(X0_47)
% 2.44/1.00      | k6_domain_1(u1_struct_0(X0_47),X0_45) = u1_struct_0(k1_tex_2(X0_47,X0_45)) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_117]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1218,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(X0_47),X0_45) = u1_struct_0(k1_tex_2(X0_47,X0_45))
% 2.44/1.00      | m1_subset_1(X0_45,u1_struct_0(X0_47)) != iProver_top
% 2.44/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.44/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5054,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(k1_tex_2(sK1,sK0(sK2)))
% 2.44/1.00      | v2_struct_0(sK1) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_5049,c_1218]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1440,plain,
% 2.44/1.00      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK2) ),
% 2.44/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1439]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1558,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
% 2.44/1.00      | v2_struct_0(sK1)
% 2.44/1.00      | ~ l1_pre_topc(sK1)
% 2.44/1.00      | k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(k1_tex_2(sK1,sK0(sK2))) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_771]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5541,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(k1_tex_2(sK1,sK0(sK2))) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_5054,c_19,c_18,c_17,c_15,c_466,c_1440,c_1498,c_1558]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5647,plain,
% 2.44/1.00      ( u1_struct_0(k1_tex_2(sK1,sK0(sK2))) = u1_struct_0(sK2) ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_5644,c_5541]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_794,plain,
% 2.44/1.00      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.44/1.00      theory(equality) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1620,plain,
% 2.44/1.00      ( g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) != X0_48
% 2.44/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_48
% 2.44/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_794]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1817,plain,
% 2.44/1.00      ( g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.44/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2))))
% 2.44/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1620]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ m1_pre_topc(X2,X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 2.44/1.00      | u1_struct_0(X2) != u1_struct_0(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_782,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.44/1.00      | ~ m1_pre_topc(X2_47,X1_47)
% 2.44/1.00      | ~ l1_pre_topc(X1_47)
% 2.44/1.00      | g1_pre_topc(u1_struct_0(X2_47),u1_pre_topc(X2_47)) = g1_pre_topc(u1_struct_0(X0_47),u1_pre_topc(X0_47))
% 2.44/1.00      | u1_struct_0(X2_47) != u1_struct_0(X0_47) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1430,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0_47,sK1)
% 2.44/1.00      | ~ m1_pre_topc(sK2,sK1)
% 2.44/1.00      | ~ l1_pre_topc(sK1)
% 2.44/1.00      | g1_pre_topc(u1_struct_0(X0_47),u1_pre_topc(X0_47)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.44/1.00      | u1_struct_0(X0_47) != u1_struct_0(sK2) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_782]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1644,plain,
% 2.44/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),sK1)
% 2.44/1.00      | ~ m1_pre_topc(sK2,sK1)
% 2.44/1.00      | ~ l1_pre_topc(sK1)
% 2.44/1.00      | g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.44/1.00      | u1_struct_0(k1_tex_2(sK1,sK0(sK2))) != u1_struct_0(sK2) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1430]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_788,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1585,plain,
% 2.44/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_788]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_14,negated_conjecture,
% 2.44/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.44/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X0)),u1_pre_topc(k1_tex_2(sK1,X0))) ),
% 2.44/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_777,negated_conjecture,
% 2.44/1.00      ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
% 2.44/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X0_45)),u1_pre_topc(k1_tex_2(sK1,X0_45))) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1573,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
% 2.44/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_777]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_780,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_47))
% 2.44/1.00      | m1_pre_topc(k1_tex_2(X0_47,X0_45),X0_47)
% 2.44/1.00      | v2_struct_0(X0_47)
% 2.44/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1560,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
% 2.44/1.00      | m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),sK1)
% 2.44/1.00      | v2_struct_0(sK1)
% 2.44/1.00      | ~ l1_pre_topc(sK1) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_780]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1461,plain,
% 2.44/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.44/1.00      | ~ l1_pre_topc(sK1)
% 2.44/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.44/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1430]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(contradiction,plain,
% 2.44/1.00      ( $false ),
% 2.44/1.00      inference(minisat,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_5647,c_1817,c_1644,c_1585,c_1573,c_1560,c_1498,c_1461,
% 2.44/1.00                 c_1440,c_466,c_15,c_17,c_18,c_19]) ).
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  ------                               Statistics
% 2.44/1.00  
% 2.44/1.00  ------ General
% 2.44/1.00  
% 2.44/1.00  abstr_ref_over_cycles:                  0
% 2.44/1.00  abstr_ref_under_cycles:                 0
% 2.44/1.00  gc_basic_clause_elim:                   0
% 2.44/1.00  forced_gc_time:                         0
% 2.44/1.00  parsing_time:                           0.011
% 2.44/1.00  unif_index_cands_time:                  0.
% 2.44/1.00  unif_index_add_time:                    0.
% 2.44/1.00  orderings_time:                         0.
% 2.44/1.00  out_proof_time:                         0.009
% 2.44/1.00  total_time:                             0.212
% 2.44/1.00  num_of_symbols:                         50
% 2.44/1.00  num_of_terms:                           2697
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing
% 2.44/1.00  
% 2.44/1.00  num_of_splits:                          0
% 2.44/1.00  num_of_split_atoms:                     0
% 2.44/1.00  num_of_reused_defs:                     0
% 2.44/1.00  num_eq_ax_congr_red:                    10
% 2.44/1.00  num_of_sem_filtered_clauses:            1
% 2.44/1.00  num_of_subtypes:                        5
% 2.44/1.00  monotx_restored_types:                  0
% 2.44/1.00  sat_num_of_epr_types:                   0
% 2.44/1.00  sat_num_of_non_cyclic_types:            0
% 2.44/1.00  sat_guarded_non_collapsed_types:        1
% 2.44/1.00  num_pure_diseq_elim:                    0
% 2.44/1.00  simp_replaced_by:                       0
% 2.44/1.00  res_preprocessed:                       118
% 2.44/1.00  prep_upred:                             0
% 2.44/1.00  prep_unflattend:                        14
% 2.44/1.00  smt_new_axioms:                         0
% 2.44/1.00  pred_elim_cands:                        7
% 2.44/1.00  pred_elim:                              1
% 2.44/1.00  pred_elim_cl:                           1
% 2.44/1.00  pred_elim_cycles:                       8
% 2.44/1.00  merged_defs:                            0
% 2.44/1.00  merged_defs_ncl:                        0
% 2.44/1.00  bin_hyper_res:                          0
% 2.44/1.00  prep_cycles:                            4
% 2.44/1.00  pred_elim_time:                         0.007
% 2.44/1.00  splitting_time:                         0.
% 2.44/1.00  sem_filter_time:                        0.
% 2.44/1.00  monotx_time:                            0.
% 2.44/1.00  subtype_inf_time:                       0.
% 2.44/1.00  
% 2.44/1.00  ------ Problem properties
% 2.44/1.00  
% 2.44/1.00  clauses:                                19
% 2.44/1.00  conjectures:                            6
% 2.44/1.00  epr:                                    6
% 2.44/1.00  horn:                                   10
% 2.44/1.00  ground:                                 5
% 2.44/1.00  unary:                                  5
% 2.44/1.00  binary:                                 1
% 2.44/1.00  lits:                                   64
% 2.44/1.00  lits_eq:                                9
% 2.44/1.00  fd_pure:                                0
% 2.44/1.00  fd_pseudo:                              0
% 2.44/1.00  fd_cond:                                0
% 2.44/1.00  fd_pseudo_cond:                         1
% 2.44/1.00  ac_symbols:                             0
% 2.44/1.00  
% 2.44/1.00  ------ Propositional Solver
% 2.44/1.00  
% 2.44/1.00  prop_solver_calls:                      32
% 2.44/1.00  prop_fast_solver_calls:                 1226
% 2.44/1.00  smt_solver_calls:                       0
% 2.44/1.00  smt_fast_solver_calls:                  0
% 2.44/1.00  prop_num_of_clauses:                    1407
% 2.44/1.00  prop_preprocess_simplified:             4719
% 2.44/1.00  prop_fo_subsumed:                       80
% 2.44/1.00  prop_solver_time:                       0.
% 2.44/1.00  smt_solver_time:                        0.
% 2.44/1.00  smt_fast_solver_time:                   0.
% 2.44/1.00  prop_fast_solver_time:                  0.
% 2.44/1.00  prop_unsat_core_time:                   0.
% 2.44/1.00  
% 2.44/1.00  ------ QBF
% 2.44/1.00  
% 2.44/1.00  qbf_q_res:                              0
% 2.44/1.00  qbf_num_tautologies:                    0
% 2.44/1.00  qbf_prep_cycles:                        0
% 2.44/1.00  
% 2.44/1.00  ------ BMC1
% 2.44/1.00  
% 2.44/1.00  bmc1_current_bound:                     -1
% 2.44/1.00  bmc1_last_solved_bound:                 -1
% 2.44/1.00  bmc1_unsat_core_size:                   -1
% 2.44/1.00  bmc1_unsat_core_parents_size:           -1
% 2.44/1.00  bmc1_merge_next_fun:                    0
% 2.44/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation
% 2.44/1.00  
% 2.44/1.00  inst_num_of_clauses:                    448
% 2.44/1.00  inst_num_in_passive:                    58
% 2.44/1.00  inst_num_in_active:                     367
% 2.44/1.00  inst_num_in_unprocessed:                23
% 2.44/1.00  inst_num_of_loops:                      390
% 2.44/1.00  inst_num_of_learning_restarts:          0
% 2.44/1.00  inst_num_moves_active_passive:          14
% 2.44/1.00  inst_lit_activity:                      0
% 2.44/1.00  inst_lit_activity_moves:                0
% 2.44/1.00  inst_num_tautologies:                   0
% 2.44/1.00  inst_num_prop_implied:                  0
% 2.44/1.00  inst_num_existing_simplified:           0
% 2.44/1.00  inst_num_eq_res_simplified:             0
% 2.44/1.00  inst_num_child_elim:                    0
% 2.44/1.00  inst_num_of_dismatching_blockings:      169
% 2.44/1.00  inst_num_of_non_proper_insts:           653
% 2.44/1.00  inst_num_of_duplicates:                 0
% 2.44/1.00  inst_inst_num_from_inst_to_res:         0
% 2.44/1.00  inst_dismatching_checking_time:         0.
% 2.44/1.00  
% 2.44/1.00  ------ Resolution
% 2.44/1.00  
% 2.44/1.00  res_num_of_clauses:                     0
% 2.44/1.00  res_num_in_passive:                     0
% 2.44/1.00  res_num_in_active:                      0
% 2.44/1.00  res_num_of_loops:                       122
% 2.44/1.00  res_forward_subset_subsumed:            94
% 2.44/1.00  res_backward_subset_subsumed:           8
% 2.44/1.00  res_forward_subsumed:                   0
% 2.44/1.00  res_backward_subsumed:                  0
% 2.44/1.00  res_forward_subsumption_resolution:     1
% 2.44/1.00  res_backward_subsumption_resolution:    0
% 2.44/1.00  res_clause_to_clause_subsumption:       352
% 2.44/1.00  res_orphan_elimination:                 0
% 2.44/1.00  res_tautology_del:                      151
% 2.44/1.00  res_num_eq_res_simplified:              0
% 2.44/1.00  res_num_sel_changes:                    0
% 2.44/1.00  res_moves_from_active_to_pass:          0
% 2.44/1.00  
% 2.44/1.00  ------ Superposition
% 2.44/1.00  
% 2.44/1.00  sup_time_total:                         0.
% 2.44/1.00  sup_time_generating:                    0.
% 2.44/1.00  sup_time_sim_full:                      0.
% 2.44/1.00  sup_time_sim_immed:                     0.
% 2.44/1.00  
% 2.44/1.00  sup_num_of_clauses:                     129
% 2.44/1.00  sup_num_in_active:                      73
% 2.44/1.00  sup_num_in_passive:                     56
% 2.44/1.00  sup_num_of_loops:                       76
% 2.44/1.00  sup_fw_superposition:                   32
% 2.44/1.00  sup_bw_superposition:                   99
% 2.44/1.00  sup_immediate_simplified:               42
% 2.44/1.00  sup_given_eliminated:                   0
% 2.44/1.00  comparisons_done:                       0
% 2.44/1.00  comparisons_avoided:                    0
% 2.44/1.00  
% 2.44/1.00  ------ Simplifications
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  sim_fw_subset_subsumed:                 8
% 2.44/1.00  sim_bw_subset_subsumed:                 4
% 2.44/1.00  sim_fw_subsumed:                        1
% 2.44/1.00  sim_bw_subsumed:                        0
% 2.44/1.00  sim_fw_subsumption_res:                 2
% 2.44/1.00  sim_bw_subsumption_res:                 0
% 2.44/1.00  sim_tautology_del:                      1
% 2.44/1.00  sim_eq_tautology_del:                   8
% 2.44/1.00  sim_eq_res_simp:                        0
% 2.44/1.00  sim_fw_demodulated:                     0
% 2.44/1.00  sim_bw_demodulated:                     2
% 2.44/1.00  sim_light_normalised:                   34
% 2.44/1.00  sim_joinable_taut:                      0
% 2.44/1.00  sim_joinable_simp:                      0
% 2.44/1.00  sim_ac_normalised:                      0
% 2.44/1.00  sim_smt_subsumption:                    0
% 2.44/1.00  
%------------------------------------------------------------------------------
