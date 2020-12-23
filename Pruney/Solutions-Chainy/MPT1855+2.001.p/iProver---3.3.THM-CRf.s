%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:45 EST 2020

% Result     : Theorem 55.57s
% Output     : CNFRefutation 55.57s
% Verified   : 
% Statistics : Number of formulae       :  303 (5211 expanded)
%              Number of clauses        :  216 (2048 expanded)
%              Number of leaves         :   22 (1093 expanded)
%              Depth                    :   28
%              Number of atoms          : 1112 (24212 expanded)
%              Number of equality atoms :  481 (4800 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_pre_topc(sK4,X0)
        & v7_struct_0(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
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
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X2)),u1_pre_topc(k1_tex_2(sK3,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_pre_topc(X1,sK3)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X2)),u1_pre_topc(k1_tex_2(sK3,X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
    & m1_pre_topc(sK4,sK3)
    & v7_struct_0(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f64,f63])).

fof(f101,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f98,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f56])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,(
    v7_struct_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
         => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v1_tex_2(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v1_tex_2(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f94,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_tex_2(k1_tex_2(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_tex_2(k1_tex_2(X0,X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_tex_2(k1_tex_2(X0,X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_tex_2(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
     => ( v1_pre_topc(sK1(X0))
        & ~ v2_struct_0(sK1(X0))
        & m1_pre_topc(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_pre_topc(sK1(X0))
        & ~ v2_struct_0(sK1(X0))
        & m1_pre_topc(sK1(X0),X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f58])).

fof(f72,plain,(
    ! [X0] :
      ( m1_pre_topc(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f67,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X0] :
      ( v1_pre_topc(sK1(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f99,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_tex_2(X1,X0)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_tex_2(X1,X0)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_tex_2(X1,X0)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_tex_2(X1,X0)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
     => ( ~ v1_tex_2(sK2(X0),X0)
        & v1_pre_topc(sK2(X0))
        & ~ v2_struct_0(sK2(X0))
        & m1_pre_topc(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( ~ v1_tex_2(sK2(X0),X0)
        & v1_pre_topc(sK2(X0))
        & ~ v2_struct_0(sK2(X0))
        & m1_pre_topc(sK2(X0),X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f61])).

fof(f90,plain,(
    ! [X0] :
      ( m1_pre_topc(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_tex_2(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f92,plain,(
    ! [X0] :
      ( v1_pre_topc(sK2(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f103,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_tex_2(X0,X1) = X2
      | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f102,plain,(
    ! [X2] :
      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X2)),u1_pre_topc(k1_tex_2(sK3,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1780,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_2460,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1780])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1801,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2439,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_2850,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2460,c_2439])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_38,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3095,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2850,c_38])).

cnf(c_0,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1803,plain,
    ( m1_subset_1(sK0(X0_51),X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2437,plain,
    ( m1_subset_1(sK0(X0_51),X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1803])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1796,plain,
    ( ~ m1_subset_1(X0_52,X0_51)
    | v1_xboole_0(X0_51)
    | k6_domain_1(X0_51,X0_52) = k1_tarski(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2444,plain,
    ( k6_domain_1(X0_51,X0_52) = k1_tarski(X0_52)
    | m1_subset_1(X0_52,X0_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1796])).

cnf(c_3668,plain,
    ( k6_domain_1(X0_51,sK0(X0_51)) = k1_tarski(sK0(X0_51))
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_2444])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_420,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_1773,plain,
    ( v2_struct_0(X0_50)
    | ~ v1_xboole_0(u1_struct_0(X0_50))
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_420])).

cnf(c_2467,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1773])).

cnf(c_5602,plain,
    ( k6_domain_1(u1_struct_0(X0_50),sK0(u1_struct_0(X0_50))) = k1_tarski(sK0(u1_struct_0(X0_50)))
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_3668,c_2467])).

cnf(c_40266,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4))) = k1_tarski(sK0(u1_struct_0(sK4)))
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3095,c_5602])).

cnf(c_33,negated_conjecture,
    ( v7_struct_0(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1779,negated_conjecture,
    ( v7_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_2461,plain,
    ( v7_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1779])).

cnf(c_18,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1791,plain,
    ( m1_pre_topc(k1_tex_2(X0_50,X0_52),X0_50)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2449,plain,
    ( m1_pre_topc(k1_tex_2(X0_50,X0_52),X0_50) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1791])).

cnf(c_28,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1783,plain,
    ( v1_tex_2(X0_50,X1_50)
    | ~ m1_pre_topc(X0_50,X1_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = g1_pre_topc(u1_struct_0(X1_50),u1_pre_topc(X1_50)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2457,plain,
    ( g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = g1_pre_topc(u1_struct_0(X1_50),u1_pre_topc(X1_50))
    | v1_tex_2(X0_50,X1_50) = iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1783])).

cnf(c_4381,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,X0_52)),u1_pre_topc(k1_tex_2(X0_50,X0_52))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
    | v1_tex_2(k1_tex_2(X0_50,X0_52),X0_50) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2449,c_2457])).

cnf(c_30,plain,
    ( ~ v1_tex_2(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1782,plain,
    ( ~ v1_tex_2(k1_tex_2(X0_50,X0_52),X0_50)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
    | ~ v7_struct_0(X0_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2458,plain,
    ( v1_tex_2(k1_tex_2(X0_50,X0_52),X0_50) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | v7_struct_0(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1782])).

cnf(c_11959,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,X0_52)),u1_pre_topc(k1_tex_2(X0_50,X0_52))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | v7_struct_0(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_4381,c_2458])).

cnf(c_19449,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))),u1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
    | v7_struct_0(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_11959])).

cnf(c_20234,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_19449])).

cnf(c_8,plain,
    ( m1_pre_topc(sK1(X0),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1798,plain,
    ( m1_pre_topc(sK1(X0_50),X0_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2442,plain,
    ( m1_pre_topc(sK1(X0_50),X0_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1798])).

cnf(c_3090,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2442,c_2439])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1802,plain,
    ( ~ l1_pre_topc(X0_50)
    | ~ v1_pre_topc(X0_50)
    | g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2438,plain,
    ( g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = X0_50
    | l1_pre_topc(X0_50) != iProver_top
    | v1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1802])).

cnf(c_5701,plain,
    ( g1_pre_topc(u1_struct_0(sK1(X0_50)),u1_pre_topc(sK1(X0_50))) = sK1(X0_50)
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_pre_topc(sK1(X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3090,c_2438])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(sK1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1800,plain,
    ( v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50)
    | v1_pre_topc(sK1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1851,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_pre_topc(sK1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_2809,plain,
    ( ~ l1_pre_topc(sK1(X0_50))
    | ~ v1_pre_topc(sK1(X0_50))
    | g1_pre_topc(u1_struct_0(sK1(X0_50)),u1_pre_topc(sK1(X0_50))) = sK1(X0_50) ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_2810,plain,
    ( g1_pre_topc(u1_struct_0(sK1(X0_50)),u1_pre_topc(sK1(X0_50))) = sK1(X0_50)
    | l1_pre_topc(sK1(X0_50)) != iProver_top
    | v1_pre_topc(sK1(X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2809])).

cnf(c_9288,plain,
    ( l1_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | g1_pre_topc(u1_struct_0(sK1(X0_50)),u1_pre_topc(sK1(X0_50))) = sK1(X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5701,c_1851,c_2810,c_3090])).

cnf(c_9289,plain,
    ( g1_pre_topc(u1_struct_0(sK1(X0_50)),u1_pre_topc(sK1(X0_50))) = sK1(X0_50)
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_9288])).

cnf(c_9298,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK4)),u1_pre_topc(sK1(sK4))) = sK1(sK4)
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3095,c_9289])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_39,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9605,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK4)),u1_pre_topc(sK1(sK4))) = sK1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9298,c_39])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1795,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)),X1_50)
    | ~ l1_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2445,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)),X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1795])).

cnf(c_4382,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)))) = g1_pre_topc(u1_struct_0(X1_50),u1_pre_topc(X1_50))
    | v1_tex_2(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)),X1_50) = iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2445,c_2457])).

cnf(c_12625,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1(sK4)),u1_pre_topc(sK1(sK4)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1(sK4)),u1_pre_topc(sK1(sK4))))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
    | v1_tex_2(sK1(sK4),X0_50) = iProver_top
    | m1_pre_topc(sK1(sK4),X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_9605,c_4382])).

cnf(c_12670,plain,
    ( g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = sK1(sK4)
    | v1_tex_2(sK1(sK4),X0_50) = iProver_top
    | m1_pre_topc(sK1(sK4),X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12625,c_9605])).

cnf(c_13683,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK1(sK4)
    | v1_tex_2(sK1(sK4),sK4) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2442,c_12670])).

cnf(c_27,plain,
    ( m1_pre_topc(sK2(X0),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1784,plain,
    ( m1_pre_topc(sK2(X0_50),X0_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2456,plain,
    ( m1_pre_topc(sK2(X0_50),X0_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1784])).

cnf(c_4380,plain,
    ( g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
    | v1_tex_2(sK2(X0_50),X0_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2456,c_2457])).

cnf(c_24,plain,
    ( ~ v1_tex_2(sK2(X0),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1787,plain,
    ( ~ v1_tex_2(sK2(X0_50),X0_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1876,plain,
    ( v1_tex_2(sK2(X0_50),X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1787])).

cnf(c_10132,plain,
    ( g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4380,c_1876])).

cnf(c_10142,plain,
    ( g1_pre_topc(u1_struct_0(sK2(sK4)),u1_pre_topc(sK2(sK4))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3095,c_10132])).

cnf(c_3645,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK2(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2456,c_2439])).

cnf(c_5709,plain,
    ( g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = sK2(X0_50)
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_pre_topc(sK2(X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3645,c_2438])).

cnf(c_25,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(sK2(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1786,plain,
    ( v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50)
    | v1_pre_topc(sK2(X0_50)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1877,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_pre_topc(sK2(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1786])).

cnf(c_2804,plain,
    ( ~ l1_pre_topc(sK2(X0_50))
    | ~ v1_pre_topc(sK2(X0_50))
    | g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = sK2(X0_50) ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_2805,plain,
    ( g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = sK2(X0_50)
    | l1_pre_topc(sK2(X0_50)) != iProver_top
    | v1_pre_topc(sK2(X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2804])).

cnf(c_9448,plain,
    ( l1_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = sK2(X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5709,c_1877,c_2805,c_3645])).

cnf(c_9449,plain,
    ( g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = sK2(X0_50)
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_9448])).

cnf(c_9458,plain,
    ( g1_pre_topc(u1_struct_0(sK2(sK4)),u1_pre_topc(sK2(sK4))) = sK2(sK4)
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3095,c_9449])).

cnf(c_9618,plain,
    ( g1_pre_topc(u1_struct_0(sK2(sK4)),u1_pre_topc(sK2(sK4))) = sK2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9458,c_39])).

cnf(c_10207,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK2(sK4)
    | v2_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10142,c_9618])).

cnf(c_11003,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10207,c_39])).

cnf(c_13684,plain,
    ( sK2(sK4) = sK1(sK4)
    | v1_tex_2(sK1(sK4),sK4) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13683,c_11003])).

cnf(c_40,plain,
    ( v7_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3740,plain,
    ( m1_pre_topc(sK1(sK4),sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_3741,plain,
    ( m1_pre_topc(sK1(sK4),sK4) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3740])).

cnf(c_14,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1793,plain,
    ( ~ v1_tex_2(X0_50,X1_50)
    | ~ m1_pre_topc(X0_50,X1_50)
    | ~ v7_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2861,plain,
    ( ~ v1_tex_2(X0_50,sK4)
    | ~ m1_pre_topc(X0_50,sK4)
    | ~ v7_struct_0(sK4)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_5781,plain,
    ( ~ v1_tex_2(sK1(sK4),sK4)
    | ~ m1_pre_topc(sK1(sK4),sK4)
    | ~ v7_struct_0(sK4)
    | v2_struct_0(sK1(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2861])).

cnf(c_5782,plain,
    ( v1_tex_2(sK1(sK4),sK4) != iProver_top
    | m1_pre_topc(sK1(sK4),sK4) != iProver_top
    | v7_struct_0(sK4) != iProver_top
    | v2_struct_0(sK1(sK4)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5781])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(sK1(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1799,plain,
    ( v2_struct_0(X0_50)
    | ~ v2_struct_0(sK1(X0_50))
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_9046,plain,
    ( ~ v2_struct_0(sK1(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_9047,plain,
    ( v2_struct_0(sK1(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9046])).

cnf(c_13952,plain,
    ( sK2(sK4) = sK1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13684,c_38,c_39,c_40,c_2850,c_3741,c_5782,c_9047])).

cnf(c_13969,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK1(sK4) ),
    inference(demodulation,[status(thm)],[c_13952,c_11003])).

cnf(c_4258,plain,
    ( m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_50,X0_52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2449,c_2439])).

cnf(c_8274,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_4258])).

cnf(c_9200,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))),u1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))))) = k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8274,c_2438])).

cnf(c_2815,plain,
    ( m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1803])).

cnf(c_2820,plain,
    ( m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2815])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_tex_2(X1,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1790,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50)
    | v1_pre_topc(k1_tex_2(X0_50,X0_52)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2951,plain,
    ( ~ m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X0_50))
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50)
    | v1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))) ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_2956,plain,
    ( m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X0_50)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2951])).

cnf(c_19180,plain,
    ( l1_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))),u1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))))) = k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9200,c_2820,c_2956])).

cnf(c_19181,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))),u1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))))) = k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_19180])).

cnf(c_19190,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK4,sK0(u1_struct_0(sK4)))
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3095,c_19181])).

cnf(c_19524,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK4,sK0(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19190,c_39])).

cnf(c_20264,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))) = sK1(sK4)
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20234,c_13969,c_19524])).

cnf(c_20265,plain,
    ( k1_tex_2(sK4,sK0(u1_struct_0(sK4))) = sK1(sK4)
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20264,c_19524])).

cnf(c_2856,plain,
    ( ~ v1_tex_2(k1_tex_2(sK4,X0_52),sK4)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ v7_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_3018,plain,
    ( ~ v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),sK4)
    | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ v7_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2856])).

cnf(c_3020,plain,
    ( v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),sK4) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | v7_struct_0(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3018])).

cnf(c_3019,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2815])).

cnf(c_3022,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3019])).

cnf(c_19527,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))))),u1_pre_topc(g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
    | v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),X0_50) = iProver_top
    | m1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_19524,c_4382])).

cnf(c_19567,plain,
    ( g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = k1_tex_2(sK4,sK0(u1_struct_0(sK4)))
    | v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),X0_50) = iProver_top
    | m1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19527,c_19524])).

cnf(c_19865,plain,
    ( k1_tex_2(sK4,sK0(u1_struct_0(sK4))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),sK4) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2449,c_19567])).

cnf(c_19866,plain,
    ( k1_tex_2(sK4,sK0(u1_struct_0(sK4))) = sK1(sK4)
    | v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),sK4) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19865,c_13969])).

cnf(c_20875,plain,
    ( k1_tex_2(sK4,sK0(u1_struct_0(sK4))) = sK1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20265,c_38,c_39,c_40,c_2850,c_3020,c_3022,c_19866])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_18])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_222])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_228,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_23,c_21])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_1775,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50)
    | k6_domain_1(u1_struct_0(X0_50),X0_52) = u1_struct_0(k1_tex_2(X0_50,X0_52)) ),
    inference(subtyping,[status(esa)],[c_229])).

cnf(c_2465,plain,
    ( k6_domain_1(u1_struct_0(X0_50),X0_52) = u1_struct_0(k1_tex_2(X0_50,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_6544,plain,
    ( k6_domain_1(u1_struct_0(X0_50),sK0(u1_struct_0(X0_50))) = u1_struct_0(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))))
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_2465])).

cnf(c_8088,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4))) = u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3095,c_6544])).

cnf(c_8379,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4))) = u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8088,c_39])).

cnf(c_20882,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4))) = u1_struct_0(sK1(sK4)) ),
    inference(demodulation,[status(thm)],[c_20875,c_8379])).

cnf(c_40449,plain,
    ( k1_tarski(sK0(u1_struct_0(sK4))) = u1_struct_0(sK1(sK4))
    | v2_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_40266,c_20882])).

cnf(c_42254,plain,
    ( k1_tarski(sK0(u1_struct_0(sK4))) = u1_struct_0(sK1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40449,c_39])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1797,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
    | m1_subset_1(X0_52,u1_struct_0(X1_50))
    | v2_struct_0(X0_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2443,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1797])).

cnf(c_3519,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_2443])).

cnf(c_9099,plain,
    ( k6_domain_1(u1_struct_0(X0_50),sK0(u1_struct_0(X1_50))) = k1_tarski(sK0(u1_struct_0(X1_50)))
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_3519,c_2444])).

cnf(c_1898,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1773])).

cnf(c_15532,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | k6_domain_1(u1_struct_0(X0_50),sK0(u1_struct_0(X1_50))) = k1_tarski(sK0(u1_struct_0(X1_50)))
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9099,c_1898])).

cnf(c_15533,plain,
    ( k6_domain_1(u1_struct_0(X0_50),sK0(u1_struct_0(X1_50))) = k1_tarski(sK0(u1_struct_0(X1_50)))
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_15532])).

cnf(c_15543,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK4))) = k1_tarski(sK0(u1_struct_0(sK4)))
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2460,c_15533])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_116,plain,
    ( v2_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_120,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2885,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1797])).

cnf(c_3151,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3))
    | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2885])).

cnf(c_3553,plain,
    ( ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK4))) = k1_tarski(sK0(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1796])).

cnf(c_15628,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK4))) = k1_tarski(sK0(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15543,c_36,c_35,c_34,c_32,c_116,c_120,c_3019,c_3151,c_3553])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X0)
    | k1_tex_2(X1,X2) = X0
    | k6_domain_1(u1_struct_0(X1),X2) != u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1792,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_subset_1(X0_52,u1_struct_0(X1_50))
    | v2_struct_0(X0_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v1_pre_topc(X0_50)
    | k6_domain_1(u1_struct_0(X1_50),X0_52) != u1_struct_0(X0_50)
    | k1_tex_2(X1_50,X0_52) = X0_50 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2448,plain,
    ( k6_domain_1(u1_struct_0(X0_50),X0_52) != u1_struct_0(X1_50)
    | k1_tex_2(X0_50,X0_52) = X1_50
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

cnf(c_15631,plain,
    ( k1_tarski(sK0(u1_struct_0(sK4))) != u1_struct_0(X0_50)
    | k1_tex_2(sK3,sK0(u1_struct_0(sK4))) = X0_50
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_15628,c_2448])).

cnf(c_37,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_41,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3153,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3151])).

cnf(c_16155,plain,
    ( m1_pre_topc(X0_50,sK3) != iProver_top
    | k1_tex_2(sK3,sK0(u1_struct_0(sK4))) = X0_50
    | k1_tarski(sK0(u1_struct_0(sK4))) != u1_struct_0(X0_50)
    | v2_struct_0(X0_50) = iProver_top
    | v1_pre_topc(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15631,c_37,c_38,c_39,c_41,c_3022,c_3153])).

cnf(c_16156,plain,
    ( k1_tarski(sK0(u1_struct_0(sK4))) != u1_struct_0(X0_50)
    | k1_tex_2(sK3,sK0(u1_struct_0(sK4))) = X0_50
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v1_pre_topc(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_16155])).

cnf(c_42303,plain,
    ( u1_struct_0(sK1(sK4)) != u1_struct_0(X0_50)
    | k1_tex_2(sK3,sK0(u1_struct_0(sK4))) = X0_50
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v1_pre_topc(X0_50) != iProver_top ),
    inference(demodulation,[status(thm)],[c_42254,c_16156])).

cnf(c_44758,plain,
    ( k1_tex_2(sK3,sK0(u1_struct_0(sK4))) = sK1(sK4)
    | m1_pre_topc(sK1(sK4),sK3) != iProver_top
    | v2_struct_0(sK1(sK4)) = iProver_top
    | v1_pre_topc(sK1(sK4)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_42303])).

cnf(c_9098,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X1_50,X2_50) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X2_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_3519,c_2443])).

cnf(c_24172,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X1_50,X2_50) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X2_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X2_50) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9098,c_2439])).

cnf(c_24174,plain,
    ( m1_pre_topc(sK3,X0_50) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(X0_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2460,c_24172])).

cnf(c_24422,plain,
    ( m1_pre_topc(sK3,X0_50) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(X0_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24174,c_37,c_39])).

cnf(c_24439,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK3,X0_50) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_24422,c_2443])).

cnf(c_1850,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_25860,plain,
    ( v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(X1_50)) = iProver_top
    | m1_pre_topc(sK3,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24439,c_1850])).

cnf(c_25861,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK3,X0_50) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_25860])).

cnf(c_25870,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2460,c_25861])).

cnf(c_25960,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25870,c_37,c_38,c_39,c_41,c_3022,c_3153])).

cnf(c_25968,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK4))) = u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_25960,c_2465])).

cnf(c_26000,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = k1_tarski(sK0(u1_struct_0(sK4)))
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25968,c_15628])).

cnf(c_27001,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = k1_tarski(sK0(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26000,c_37,c_38])).

cnf(c_31,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X0)),u1_pre_topc(k1_tex_2(sK3,X0))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1781,negated_conjecture,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X0_52)),u1_pre_topc(k1_tex_2(sK3,X0_52))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2459,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X0_52)),u1_pre_topc(k1_tex_2(sK3,X0_52)))
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1781])).

cnf(c_11015,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X0_52)),u1_pre_topc(k1_tex_2(sK3,X0_52))) != sK2(sK4)
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11003,c_2459])).

cnf(c_13967,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X0_52)),u1_pre_topc(k1_tex_2(sK3,X0_52))) != sK1(sK4)
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13952,c_11015])).

cnf(c_27057,plain,
    ( g1_pre_topc(k1_tarski(sK0(u1_struct_0(sK4))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) != sK1(sK4)
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27001,c_13967])).

cnf(c_28372,plain,
    ( g1_pre_topc(k1_tarski(sK0(u1_struct_0(sK4))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) != sK1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27057,c_37,c_38,c_39,c_41,c_3022,c_3153])).

cnf(c_25967,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_25960,c_4258])).

cnf(c_3533,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),sK3)
    | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1791])).

cnf(c_3543,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),sK3) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3533])).

cnf(c_5221,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),X0_50)
    | ~ l1_pre_topc(X0_50)
    | l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) ),
    inference(instantiation,[status(thm)],[c_1801])).

cnf(c_5222,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5221])).

cnf(c_5224,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),sK3) != iProver_top
    | l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5222])).

cnf(c_26181,plain,
    ( l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25967,c_37,c_38,c_39,c_41,c_3022,c_3153,c_3543,c_5224])).

cnf(c_26196,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK3,sK0(u1_struct_0(sK4)))
    | v1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26181,c_2438])).

cnf(c_3534,plain,
    ( ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_3797,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))
    | ~ v1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))
    | g1_pre_topc(u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK3,sK0(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_5223,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),sK3)
    | l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_5221])).

cnf(c_27780,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK3,sK0(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26196,c_36,c_35,c_34,c_32,c_3019,c_3151,c_3534,c_3533,c_3797,c_5223])).

cnf(c_27782,plain,
    ( g1_pre_topc(k1_tarski(sK0(u1_struct_0(sK4))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK3,sK0(u1_struct_0(sK4))) ),
    inference(light_normalisation,[status(thm)],[c_27780,c_27001])).

cnf(c_28374,plain,
    ( k1_tex_2(sK3,sK0(u1_struct_0(sK4))) != sK1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_28372,c_27782])).

cnf(c_11059,plain,
    ( m1_pre_topc(sK2(sK4),X0_50) = iProver_top
    | m1_pre_topc(sK4,X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_11003,c_2445])).

cnf(c_13968,plain,
    ( m1_pre_topc(sK1(sK4),X0_50) = iProver_top
    | m1_pre_topc(sK4,X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13952,c_11059])).

cnf(c_14033,plain,
    ( m1_pre_topc(sK1(sK4),sK3) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13968])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1794,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2446,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1794])).

cnf(c_3496,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2460,c_2446])).

cnf(c_2786,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_2787,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2786])).

cnf(c_3834,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3496,c_38,c_41,c_2787])).

cnf(c_11013,plain,
    ( v1_pre_topc(sK2(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11003,c_3834])).

cnf(c_13965,plain,
    ( v1_pre_topc(sK1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13952,c_11013])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44758,c_28374,c_14033,c_13965,c_9047,c_2850,c_41,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 55.57/7.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.57/7.50  
% 55.57/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.57/7.50  
% 55.57/7.50  ------  iProver source info
% 55.57/7.50  
% 55.57/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.57/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.57/7.50  git: non_committed_changes: false
% 55.57/7.50  git: last_make_outside_of_git: false
% 55.57/7.50  
% 55.57/7.50  ------ 
% 55.57/7.50  
% 55.57/7.50  ------ Input Options
% 55.57/7.50  
% 55.57/7.50  --out_options                           all
% 55.57/7.50  --tptp_safe_out                         true
% 55.57/7.50  --problem_path                          ""
% 55.57/7.50  --include_path                          ""
% 55.57/7.50  --clausifier                            res/vclausify_rel
% 55.57/7.50  --clausifier_options                    --mode clausify
% 55.57/7.50  --stdin                                 false
% 55.57/7.50  --stats_out                             all
% 55.57/7.50  
% 55.57/7.50  ------ General Options
% 55.57/7.50  
% 55.57/7.50  --fof                                   false
% 55.57/7.50  --time_out_real                         305.
% 55.57/7.50  --time_out_virtual                      -1.
% 55.57/7.50  --symbol_type_check                     false
% 55.57/7.50  --clausify_out                          false
% 55.57/7.50  --sig_cnt_out                           false
% 55.57/7.50  --trig_cnt_out                          false
% 55.57/7.50  --trig_cnt_out_tolerance                1.
% 55.57/7.50  --trig_cnt_out_sk_spl                   false
% 55.57/7.50  --abstr_cl_out                          false
% 55.57/7.50  
% 55.57/7.50  ------ Global Options
% 55.57/7.50  
% 55.57/7.50  --schedule                              default
% 55.57/7.50  --add_important_lit                     false
% 55.57/7.50  --prop_solver_per_cl                    1000
% 55.57/7.50  --min_unsat_core                        false
% 55.57/7.50  --soft_assumptions                      false
% 55.57/7.50  --soft_lemma_size                       3
% 55.57/7.50  --prop_impl_unit_size                   0
% 55.57/7.50  --prop_impl_unit                        []
% 55.57/7.50  --share_sel_clauses                     true
% 55.57/7.50  --reset_solvers                         false
% 55.57/7.50  --bc_imp_inh                            [conj_cone]
% 55.57/7.50  --conj_cone_tolerance                   3.
% 55.57/7.50  --extra_neg_conj                        none
% 55.57/7.50  --large_theory_mode                     true
% 55.57/7.50  --prolific_symb_bound                   200
% 55.57/7.50  --lt_threshold                          2000
% 55.57/7.50  --clause_weak_htbl                      true
% 55.57/7.50  --gc_record_bc_elim                     false
% 55.57/7.50  
% 55.57/7.50  ------ Preprocessing Options
% 55.57/7.50  
% 55.57/7.50  --preprocessing_flag                    true
% 55.57/7.50  --time_out_prep_mult                    0.1
% 55.57/7.50  --splitting_mode                        input
% 55.57/7.50  --splitting_grd                         true
% 55.57/7.50  --splitting_cvd                         false
% 55.57/7.50  --splitting_cvd_svl                     false
% 55.57/7.50  --splitting_nvd                         32
% 55.57/7.50  --sub_typing                            true
% 55.57/7.50  --prep_gs_sim                           true
% 55.57/7.50  --prep_unflatten                        true
% 55.57/7.50  --prep_res_sim                          true
% 55.57/7.50  --prep_upred                            true
% 55.57/7.50  --prep_sem_filter                       exhaustive
% 55.57/7.50  --prep_sem_filter_out                   false
% 55.57/7.50  --pred_elim                             true
% 55.57/7.50  --res_sim_input                         true
% 55.57/7.50  --eq_ax_congr_red                       true
% 55.57/7.50  --pure_diseq_elim                       true
% 55.57/7.50  --brand_transform                       false
% 55.57/7.50  --non_eq_to_eq                          false
% 55.57/7.50  --prep_def_merge                        true
% 55.57/7.50  --prep_def_merge_prop_impl              false
% 55.57/7.50  --prep_def_merge_mbd                    true
% 55.57/7.50  --prep_def_merge_tr_red                 false
% 55.57/7.50  --prep_def_merge_tr_cl                  false
% 55.57/7.50  --smt_preprocessing                     true
% 55.57/7.50  --smt_ac_axioms                         fast
% 55.57/7.50  --preprocessed_out                      false
% 55.57/7.50  --preprocessed_stats                    false
% 55.57/7.50  
% 55.57/7.50  ------ Abstraction refinement Options
% 55.57/7.50  
% 55.57/7.50  --abstr_ref                             []
% 55.57/7.50  --abstr_ref_prep                        false
% 55.57/7.50  --abstr_ref_until_sat                   false
% 55.57/7.50  --abstr_ref_sig_restrict                funpre
% 55.57/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.57/7.50  --abstr_ref_under                       []
% 55.57/7.50  
% 55.57/7.50  ------ SAT Options
% 55.57/7.50  
% 55.57/7.50  --sat_mode                              false
% 55.57/7.50  --sat_fm_restart_options                ""
% 55.57/7.50  --sat_gr_def                            false
% 55.57/7.50  --sat_epr_types                         true
% 55.57/7.50  --sat_non_cyclic_types                  false
% 55.57/7.50  --sat_finite_models                     false
% 55.57/7.50  --sat_fm_lemmas                         false
% 55.57/7.50  --sat_fm_prep                           false
% 55.57/7.50  --sat_fm_uc_incr                        true
% 55.57/7.50  --sat_out_model                         small
% 55.57/7.50  --sat_out_clauses                       false
% 55.57/7.50  
% 55.57/7.50  ------ QBF Options
% 55.57/7.50  
% 55.57/7.50  --qbf_mode                              false
% 55.57/7.50  --qbf_elim_univ                         false
% 55.57/7.50  --qbf_dom_inst                          none
% 55.57/7.50  --qbf_dom_pre_inst                      false
% 55.57/7.50  --qbf_sk_in                             false
% 55.57/7.50  --qbf_pred_elim                         true
% 55.57/7.50  --qbf_split                             512
% 55.57/7.50  
% 55.57/7.50  ------ BMC1 Options
% 55.57/7.50  
% 55.57/7.50  --bmc1_incremental                      false
% 55.57/7.50  --bmc1_axioms                           reachable_all
% 55.57/7.50  --bmc1_min_bound                        0
% 55.57/7.50  --bmc1_max_bound                        -1
% 55.57/7.50  --bmc1_max_bound_default                -1
% 55.57/7.50  --bmc1_symbol_reachability              true
% 55.57/7.50  --bmc1_property_lemmas                  false
% 55.57/7.50  --bmc1_k_induction                      false
% 55.57/7.50  --bmc1_non_equiv_states                 false
% 55.57/7.50  --bmc1_deadlock                         false
% 55.57/7.50  --bmc1_ucm                              false
% 55.57/7.50  --bmc1_add_unsat_core                   none
% 55.57/7.50  --bmc1_unsat_core_children              false
% 55.57/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.57/7.50  --bmc1_out_stat                         full
% 55.57/7.50  --bmc1_ground_init                      false
% 55.57/7.50  --bmc1_pre_inst_next_state              false
% 55.57/7.50  --bmc1_pre_inst_state                   false
% 55.57/7.50  --bmc1_pre_inst_reach_state             false
% 55.57/7.50  --bmc1_out_unsat_core                   false
% 55.57/7.50  --bmc1_aig_witness_out                  false
% 55.57/7.50  --bmc1_verbose                          false
% 55.57/7.50  --bmc1_dump_clauses_tptp                false
% 55.57/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.57/7.50  --bmc1_dump_file                        -
% 55.57/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.57/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.57/7.50  --bmc1_ucm_extend_mode                  1
% 55.57/7.50  --bmc1_ucm_init_mode                    2
% 55.57/7.50  --bmc1_ucm_cone_mode                    none
% 55.57/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.57/7.50  --bmc1_ucm_relax_model                  4
% 55.57/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.57/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.57/7.50  --bmc1_ucm_layered_model                none
% 55.57/7.50  --bmc1_ucm_max_lemma_size               10
% 55.57/7.50  
% 55.57/7.50  ------ AIG Options
% 55.57/7.50  
% 55.57/7.50  --aig_mode                              false
% 55.57/7.50  
% 55.57/7.50  ------ Instantiation Options
% 55.57/7.50  
% 55.57/7.50  --instantiation_flag                    true
% 55.57/7.50  --inst_sos_flag                         false
% 55.57/7.50  --inst_sos_phase                        true
% 55.57/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.57/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.57/7.50  --inst_lit_sel_side                     num_symb
% 55.57/7.50  --inst_solver_per_active                1400
% 55.57/7.50  --inst_solver_calls_frac                1.
% 55.57/7.50  --inst_passive_queue_type               priority_queues
% 55.57/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.57/7.50  --inst_passive_queues_freq              [25;2]
% 55.57/7.50  --inst_dismatching                      true
% 55.57/7.50  --inst_eager_unprocessed_to_passive     true
% 55.57/7.50  --inst_prop_sim_given                   true
% 55.57/7.50  --inst_prop_sim_new                     false
% 55.57/7.50  --inst_subs_new                         false
% 55.57/7.50  --inst_eq_res_simp                      false
% 55.57/7.50  --inst_subs_given                       false
% 55.57/7.50  --inst_orphan_elimination               true
% 55.57/7.50  --inst_learning_loop_flag               true
% 55.57/7.50  --inst_learning_start                   3000
% 55.57/7.50  --inst_learning_factor                  2
% 55.57/7.50  --inst_start_prop_sim_after_learn       3
% 55.57/7.50  --inst_sel_renew                        solver
% 55.57/7.50  --inst_lit_activity_flag                true
% 55.57/7.50  --inst_restr_to_given                   false
% 55.57/7.50  --inst_activity_threshold               500
% 55.57/7.50  --inst_out_proof                        true
% 55.57/7.50  
% 55.57/7.50  ------ Resolution Options
% 55.57/7.50  
% 55.57/7.50  --resolution_flag                       true
% 55.57/7.50  --res_lit_sel                           adaptive
% 55.57/7.50  --res_lit_sel_side                      none
% 55.57/7.50  --res_ordering                          kbo
% 55.57/7.50  --res_to_prop_solver                    active
% 55.57/7.50  --res_prop_simpl_new                    false
% 55.57/7.50  --res_prop_simpl_given                  true
% 55.57/7.50  --res_passive_queue_type                priority_queues
% 55.57/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.57/7.50  --res_passive_queues_freq               [15;5]
% 55.57/7.50  --res_forward_subs                      full
% 55.57/7.50  --res_backward_subs                     full
% 55.57/7.50  --res_forward_subs_resolution           true
% 55.57/7.50  --res_backward_subs_resolution          true
% 55.57/7.50  --res_orphan_elimination                true
% 55.57/7.50  --res_time_limit                        2.
% 55.57/7.50  --res_out_proof                         true
% 55.57/7.50  
% 55.57/7.50  ------ Superposition Options
% 55.57/7.50  
% 55.57/7.50  --superposition_flag                    true
% 55.57/7.50  --sup_passive_queue_type                priority_queues
% 55.57/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.57/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.57/7.50  --demod_completeness_check              fast
% 55.57/7.50  --demod_use_ground                      true
% 55.57/7.50  --sup_to_prop_solver                    passive
% 55.57/7.50  --sup_prop_simpl_new                    true
% 55.57/7.50  --sup_prop_simpl_given                  true
% 55.57/7.50  --sup_fun_splitting                     false
% 55.57/7.50  --sup_smt_interval                      50000
% 55.57/7.50  
% 55.57/7.50  ------ Superposition Simplification Setup
% 55.57/7.50  
% 55.57/7.50  --sup_indices_passive                   []
% 55.57/7.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.57/7.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.57/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.57/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.57/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.57/7.50  --sup_full_bw                           [BwDemod]
% 55.57/7.50  --sup_immed_triv                        [TrivRules]
% 55.57/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.57/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.57/7.50  --sup_immed_bw_main                     []
% 55.57/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.57/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.57/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.57/7.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.57/7.50  
% 55.57/7.50  ------ Combination Options
% 55.57/7.50  
% 55.57/7.50  --comb_res_mult                         3
% 55.57/7.50  --comb_sup_mult                         2
% 55.57/7.50  --comb_inst_mult                        10
% 55.57/7.50  
% 55.57/7.50  ------ Debug Options
% 55.57/7.50  
% 55.57/7.50  --dbg_backtrace                         false
% 55.57/7.50  --dbg_dump_prop_clauses                 false
% 55.57/7.50  --dbg_dump_prop_clauses_file            -
% 55.57/7.50  --dbg_out_stat                          false
% 55.57/7.50  ------ Parsing...
% 55.57/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.57/7.50  
% 55.57/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 55.57/7.50  
% 55.57/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.57/7.50  
% 55.57/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.57/7.50  ------ Proving...
% 55.57/7.50  ------ Problem Properties 
% 55.57/7.50  
% 55.57/7.50  
% 55.57/7.50  clauses                                 32
% 55.57/7.50  conjectures                             6
% 55.57/7.50  EPR                                     7
% 55.57/7.50  Horn                                    18
% 55.57/7.50  unary                                   6
% 55.57/7.50  binary                                  1
% 55.57/7.50  lits                                    106
% 55.57/7.50  lits eq                                 8
% 55.57/7.50  fd_pure                                 0
% 55.57/7.50  fd_pseudo                               0
% 55.57/7.50  fd_cond                                 0
% 55.57/7.50  fd_pseudo_cond                          1
% 55.57/7.50  AC symbols                              0
% 55.57/7.50  
% 55.57/7.50  ------ Schedule dynamic 5 is on 
% 55.57/7.50  
% 55.57/7.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.57/7.50  
% 55.57/7.50  
% 55.57/7.50  ------ 
% 55.57/7.50  Current options:
% 55.57/7.50  ------ 
% 55.57/7.50  
% 55.57/7.50  ------ Input Options
% 55.57/7.50  
% 55.57/7.50  --out_options                           all
% 55.57/7.50  --tptp_safe_out                         true
% 55.57/7.50  --problem_path                          ""
% 55.57/7.50  --include_path                          ""
% 55.57/7.50  --clausifier                            res/vclausify_rel
% 55.57/7.50  --clausifier_options                    --mode clausify
% 55.57/7.50  --stdin                                 false
% 55.57/7.50  --stats_out                             all
% 55.57/7.50  
% 55.57/7.50  ------ General Options
% 55.57/7.50  
% 55.57/7.50  --fof                                   false
% 55.57/7.50  --time_out_real                         305.
% 55.57/7.50  --time_out_virtual                      -1.
% 55.57/7.50  --symbol_type_check                     false
% 55.57/7.50  --clausify_out                          false
% 55.57/7.50  --sig_cnt_out                           false
% 55.57/7.50  --trig_cnt_out                          false
% 55.57/7.50  --trig_cnt_out_tolerance                1.
% 55.57/7.50  --trig_cnt_out_sk_spl                   false
% 55.57/7.50  --abstr_cl_out                          false
% 55.57/7.50  
% 55.57/7.50  ------ Global Options
% 55.57/7.50  
% 55.57/7.50  --schedule                              default
% 55.57/7.50  --add_important_lit                     false
% 55.57/7.50  --prop_solver_per_cl                    1000
% 55.57/7.50  --min_unsat_core                        false
% 55.57/7.50  --soft_assumptions                      false
% 55.57/7.50  --soft_lemma_size                       3
% 55.57/7.50  --prop_impl_unit_size                   0
% 55.57/7.50  --prop_impl_unit                        []
% 55.57/7.50  --share_sel_clauses                     true
% 55.57/7.50  --reset_solvers                         false
% 55.57/7.50  --bc_imp_inh                            [conj_cone]
% 55.57/7.50  --conj_cone_tolerance                   3.
% 55.57/7.50  --extra_neg_conj                        none
% 55.57/7.50  --large_theory_mode                     true
% 55.57/7.50  --prolific_symb_bound                   200
% 55.57/7.50  --lt_threshold                          2000
% 55.57/7.50  --clause_weak_htbl                      true
% 55.57/7.50  --gc_record_bc_elim                     false
% 55.57/7.50  
% 55.57/7.50  ------ Preprocessing Options
% 55.57/7.50  
% 55.57/7.50  --preprocessing_flag                    true
% 55.57/7.50  --time_out_prep_mult                    0.1
% 55.57/7.50  --splitting_mode                        input
% 55.57/7.50  --splitting_grd                         true
% 55.57/7.50  --splitting_cvd                         false
% 55.57/7.50  --splitting_cvd_svl                     false
% 55.57/7.50  --splitting_nvd                         32
% 55.57/7.50  --sub_typing                            true
% 55.57/7.50  --prep_gs_sim                           true
% 55.57/7.50  --prep_unflatten                        true
% 55.57/7.50  --prep_res_sim                          true
% 55.57/7.50  --prep_upred                            true
% 55.57/7.50  --prep_sem_filter                       exhaustive
% 55.57/7.50  --prep_sem_filter_out                   false
% 55.57/7.50  --pred_elim                             true
% 55.57/7.50  --res_sim_input                         true
% 55.57/7.50  --eq_ax_congr_red                       true
% 55.57/7.50  --pure_diseq_elim                       true
% 55.57/7.50  --brand_transform                       false
% 55.57/7.50  --non_eq_to_eq                          false
% 55.57/7.50  --prep_def_merge                        true
% 55.57/7.50  --prep_def_merge_prop_impl              false
% 55.57/7.50  --prep_def_merge_mbd                    true
% 55.57/7.50  --prep_def_merge_tr_red                 false
% 55.57/7.50  --prep_def_merge_tr_cl                  false
% 55.57/7.50  --smt_preprocessing                     true
% 55.57/7.50  --smt_ac_axioms                         fast
% 55.57/7.50  --preprocessed_out                      false
% 55.57/7.50  --preprocessed_stats                    false
% 55.57/7.50  
% 55.57/7.50  ------ Abstraction refinement Options
% 55.57/7.50  
% 55.57/7.50  --abstr_ref                             []
% 55.57/7.50  --abstr_ref_prep                        false
% 55.57/7.50  --abstr_ref_until_sat                   false
% 55.57/7.50  --abstr_ref_sig_restrict                funpre
% 55.57/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.57/7.50  --abstr_ref_under                       []
% 55.57/7.50  
% 55.57/7.50  ------ SAT Options
% 55.57/7.50  
% 55.57/7.50  --sat_mode                              false
% 55.57/7.50  --sat_fm_restart_options                ""
% 55.57/7.50  --sat_gr_def                            false
% 55.57/7.50  --sat_epr_types                         true
% 55.57/7.50  --sat_non_cyclic_types                  false
% 55.57/7.50  --sat_finite_models                     false
% 55.57/7.50  --sat_fm_lemmas                         false
% 55.57/7.50  --sat_fm_prep                           false
% 55.57/7.50  --sat_fm_uc_incr                        true
% 55.57/7.50  --sat_out_model                         small
% 55.57/7.50  --sat_out_clauses                       false
% 55.57/7.50  
% 55.57/7.50  ------ QBF Options
% 55.57/7.50  
% 55.57/7.50  --qbf_mode                              false
% 55.57/7.50  --qbf_elim_univ                         false
% 55.57/7.50  --qbf_dom_inst                          none
% 55.57/7.50  --qbf_dom_pre_inst                      false
% 55.57/7.50  --qbf_sk_in                             false
% 55.57/7.50  --qbf_pred_elim                         true
% 55.57/7.50  --qbf_split                             512
% 55.57/7.50  
% 55.57/7.50  ------ BMC1 Options
% 55.57/7.50  
% 55.57/7.50  --bmc1_incremental                      false
% 55.57/7.50  --bmc1_axioms                           reachable_all
% 55.57/7.50  --bmc1_min_bound                        0
% 55.57/7.50  --bmc1_max_bound                        -1
% 55.57/7.50  --bmc1_max_bound_default                -1
% 55.57/7.50  --bmc1_symbol_reachability              true
% 55.57/7.50  --bmc1_property_lemmas                  false
% 55.57/7.50  --bmc1_k_induction                      false
% 55.57/7.50  --bmc1_non_equiv_states                 false
% 55.57/7.50  --bmc1_deadlock                         false
% 55.57/7.50  --bmc1_ucm                              false
% 55.57/7.50  --bmc1_add_unsat_core                   none
% 55.57/7.50  --bmc1_unsat_core_children              false
% 55.57/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.57/7.50  --bmc1_out_stat                         full
% 55.57/7.50  --bmc1_ground_init                      false
% 55.57/7.50  --bmc1_pre_inst_next_state              false
% 55.57/7.50  --bmc1_pre_inst_state                   false
% 55.57/7.50  --bmc1_pre_inst_reach_state             false
% 55.57/7.50  --bmc1_out_unsat_core                   false
% 55.57/7.50  --bmc1_aig_witness_out                  false
% 55.57/7.50  --bmc1_verbose                          false
% 55.57/7.50  --bmc1_dump_clauses_tptp                false
% 55.57/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.57/7.50  --bmc1_dump_file                        -
% 55.57/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.57/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.57/7.50  --bmc1_ucm_extend_mode                  1
% 55.57/7.50  --bmc1_ucm_init_mode                    2
% 55.57/7.50  --bmc1_ucm_cone_mode                    none
% 55.57/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.57/7.50  --bmc1_ucm_relax_model                  4
% 55.57/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.57/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.57/7.50  --bmc1_ucm_layered_model                none
% 55.57/7.50  --bmc1_ucm_max_lemma_size               10
% 55.57/7.50  
% 55.57/7.50  ------ AIG Options
% 55.57/7.50  
% 55.57/7.50  --aig_mode                              false
% 55.57/7.50  
% 55.57/7.50  ------ Instantiation Options
% 55.57/7.50  
% 55.57/7.50  --instantiation_flag                    true
% 55.57/7.50  --inst_sos_flag                         false
% 55.57/7.50  --inst_sos_phase                        true
% 55.57/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.57/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.57/7.50  --inst_lit_sel_side                     none
% 55.57/7.50  --inst_solver_per_active                1400
% 55.57/7.50  --inst_solver_calls_frac                1.
% 55.57/7.50  --inst_passive_queue_type               priority_queues
% 55.57/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.57/7.50  --inst_passive_queues_freq              [25;2]
% 55.57/7.50  --inst_dismatching                      true
% 55.57/7.50  --inst_eager_unprocessed_to_passive     true
% 55.57/7.50  --inst_prop_sim_given                   true
% 55.57/7.50  --inst_prop_sim_new                     false
% 55.57/7.50  --inst_subs_new                         false
% 55.57/7.50  --inst_eq_res_simp                      false
% 55.57/7.50  --inst_subs_given                       false
% 55.57/7.50  --inst_orphan_elimination               true
% 55.57/7.50  --inst_learning_loop_flag               true
% 55.57/7.50  --inst_learning_start                   3000
% 55.57/7.50  --inst_learning_factor                  2
% 55.57/7.50  --inst_start_prop_sim_after_learn       3
% 55.57/7.50  --inst_sel_renew                        solver
% 55.57/7.50  --inst_lit_activity_flag                true
% 55.57/7.50  --inst_restr_to_given                   false
% 55.57/7.50  --inst_activity_threshold               500
% 55.57/7.50  --inst_out_proof                        true
% 55.57/7.50  
% 55.57/7.50  ------ Resolution Options
% 55.57/7.50  
% 55.57/7.50  --resolution_flag                       false
% 55.57/7.50  --res_lit_sel                           adaptive
% 55.57/7.50  --res_lit_sel_side                      none
% 55.57/7.50  --res_ordering                          kbo
% 55.57/7.50  --res_to_prop_solver                    active
% 55.57/7.50  --res_prop_simpl_new                    false
% 55.57/7.50  --res_prop_simpl_given                  true
% 55.57/7.50  --res_passive_queue_type                priority_queues
% 55.57/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.57/7.50  --res_passive_queues_freq               [15;5]
% 55.57/7.50  --res_forward_subs                      full
% 55.57/7.50  --res_backward_subs                     full
% 55.57/7.50  --res_forward_subs_resolution           true
% 55.57/7.50  --res_backward_subs_resolution          true
% 55.57/7.50  --res_orphan_elimination                true
% 55.57/7.50  --res_time_limit                        2.
% 55.57/7.50  --res_out_proof                         true
% 55.57/7.50  
% 55.57/7.50  ------ Superposition Options
% 55.57/7.50  
% 55.57/7.50  --superposition_flag                    true
% 55.57/7.50  --sup_passive_queue_type                priority_queues
% 55.57/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.57/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.57/7.50  --demod_completeness_check              fast
% 55.57/7.50  --demod_use_ground                      true
% 55.57/7.50  --sup_to_prop_solver                    passive
% 55.57/7.50  --sup_prop_simpl_new                    true
% 55.57/7.50  --sup_prop_simpl_given                  true
% 55.57/7.50  --sup_fun_splitting                     false
% 55.57/7.50  --sup_smt_interval                      50000
% 55.57/7.50  
% 55.57/7.50  ------ Superposition Simplification Setup
% 55.57/7.50  
% 55.57/7.50  --sup_indices_passive                   []
% 55.57/7.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.57/7.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.57/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.57/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.57/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.57/7.50  --sup_full_bw                           [BwDemod]
% 55.57/7.50  --sup_immed_triv                        [TrivRules]
% 55.57/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.57/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.57/7.50  --sup_immed_bw_main                     []
% 55.57/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.57/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.57/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.57/7.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.57/7.50  
% 55.57/7.50  ------ Combination Options
% 55.57/7.50  
% 55.57/7.50  --comb_res_mult                         3
% 55.57/7.50  --comb_sup_mult                         2
% 55.57/7.50  --comb_inst_mult                        10
% 55.57/7.50  
% 55.57/7.50  ------ Debug Options
% 55.57/7.50  
% 55.57/7.50  --dbg_backtrace                         false
% 55.57/7.50  --dbg_dump_prop_clauses                 false
% 55.57/7.50  --dbg_dump_prop_clauses_file            -
% 55.57/7.50  --dbg_out_stat                          false
% 55.57/7.50  
% 55.57/7.50  
% 55.57/7.50  
% 55.57/7.50  
% 55.57/7.50  ------ Proving...
% 55.57/7.50  
% 55.57/7.50  
% 55.57/7.50  % SZS status Theorem for theBenchmark.p
% 55.57/7.50  
% 55.57/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.57/7.50  
% 55.57/7.50  fof(f20,conjecture,(
% 55.57/7.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f21,negated_conjecture,(
% 55.57/7.50    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 55.57/7.50    inference(negated_conjecture,[],[f20])).
% 55.57/7.50  
% 55.57/7.50  fof(f54,plain,(
% 55.57/7.50    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & (m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f21])).
% 55.57/7.50  
% 55.57/7.50  fof(f55,plain,(
% 55.57/7.50    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 55.57/7.50    inference(flattening,[],[f54])).
% 55.57/7.50  
% 55.57/7.50  fof(f64,plain,(
% 55.57/7.50    ( ! [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (! [X2] : (g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(sK4,X0) & v7_struct_0(sK4) & ~v2_struct_0(sK4))) )),
% 55.57/7.50    introduced(choice_axiom,[])).
% 55.57/7.50  
% 55.57/7.50  fof(f63,plain,(
% 55.57/7.50    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X2)),u1_pre_topc(k1_tex_2(sK3,X2))) | ~m1_subset_1(X2,u1_struct_0(sK3))) & m1_pre_topc(X1,sK3) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 55.57/7.50    introduced(choice_axiom,[])).
% 55.57/7.50  
% 55.57/7.50  fof(f65,plain,(
% 55.57/7.50    (! [X2] : (g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X2)),u1_pre_topc(k1_tex_2(sK3,X2))) | ~m1_subset_1(X2,u1_struct_0(sK3))) & m1_pre_topc(sK4,sK3) & v7_struct_0(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 55.57/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f64,f63])).
% 55.57/7.50  
% 55.57/7.50  fof(f101,plain,(
% 55.57/7.50    m1_pre_topc(sK4,sK3)),
% 55.57/7.50    inference(cnf_transformation,[],[f65])).
% 55.57/7.50  
% 55.57/7.50  fof(f4,axiom,(
% 55.57/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f25,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 55.57/7.50    inference(ennf_transformation,[],[f4])).
% 55.57/7.50  
% 55.57/7.50  fof(f69,plain,(
% 55.57/7.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f25])).
% 55.57/7.50  
% 55.57/7.50  fof(f98,plain,(
% 55.57/7.50    l1_pre_topc(sK3)),
% 55.57/7.50    inference(cnf_transformation,[],[f65])).
% 55.57/7.50  
% 55.57/7.50  fof(f1,axiom,(
% 55.57/7.50    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f56,plain,(
% 55.57/7.50    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 55.57/7.50    introduced(choice_axiom,[])).
% 55.57/7.50  
% 55.57/7.50  fof(f57,plain,(
% 55.57/7.50    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 55.57/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f56])).
% 55.57/7.50  
% 55.57/7.50  fof(f66,plain,(
% 55.57/7.50    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f57])).
% 55.57/7.50  
% 55.57/7.50  fof(f9,axiom,(
% 55.57/7.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f34,plain,(
% 55.57/7.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f9])).
% 55.57/7.50  
% 55.57/7.50  fof(f35,plain,(
% 55.57/7.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 55.57/7.50    inference(flattening,[],[f34])).
% 55.57/7.50  
% 55.57/7.50  fof(f76,plain,(
% 55.57/7.50    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f35])).
% 55.57/7.50  
% 55.57/7.50  fof(f3,axiom,(
% 55.57/7.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f24,plain,(
% 55.57/7.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 55.57/7.50    inference(ennf_transformation,[],[f3])).
% 55.57/7.50  
% 55.57/7.50  fof(f68,plain,(
% 55.57/7.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f24])).
% 55.57/7.50  
% 55.57/7.50  fof(f5,axiom,(
% 55.57/7.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f26,plain,(
% 55.57/7.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f5])).
% 55.57/7.50  
% 55.57/7.50  fof(f27,plain,(
% 55.57/7.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(flattening,[],[f26])).
% 55.57/7.50  
% 55.57/7.50  fof(f70,plain,(
% 55.57/7.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f27])).
% 55.57/7.50  
% 55.57/7.50  fof(f100,plain,(
% 55.57/7.50    v7_struct_0(sK4)),
% 55.57/7.50    inference(cnf_transformation,[],[f65])).
% 55.57/7.50  
% 55.57/7.50  fof(f14,axiom,(
% 55.57/7.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f42,plain,(
% 55.57/7.50    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f14])).
% 55.57/7.50  
% 55.57/7.50  fof(f43,plain,(
% 55.57/7.50    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(flattening,[],[f42])).
% 55.57/7.50  
% 55.57/7.50  fof(f86,plain,(
% 55.57/7.50    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f43])).
% 55.57/7.50  
% 55.57/7.50  fof(f17,axiom,(
% 55.57/7.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f48,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f17])).
% 55.57/7.50  
% 55.57/7.50  fof(f49,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(flattening,[],[f48])).
% 55.57/7.50  
% 55.57/7.50  fof(f94,plain,(
% 55.57/7.50    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f49])).
% 55.57/7.50  
% 55.57/7.50  fof(f19,axiom,(
% 55.57/7.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_tex_2(k1_tex_2(X0,X1),X0))))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f52,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f19])).
% 55.57/7.50  
% 55.57/7.50  fof(f53,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_tex_2(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(flattening,[],[f52])).
% 55.57/7.50  
% 55.57/7.50  fof(f96,plain,(
% 55.57/7.50    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_tex_2(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f53])).
% 55.57/7.50  
% 55.57/7.50  fof(f7,axiom,(
% 55.57/7.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f30,plain,(
% 55.57/7.50    ! [X0] : (? [X1] : (v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f7])).
% 55.57/7.50  
% 55.57/7.50  fof(f31,plain,(
% 55.57/7.50    ! [X0] : (? [X1] : (v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(flattening,[],[f30])).
% 55.57/7.50  
% 55.57/7.50  fof(f58,plain,(
% 55.57/7.50    ! [X0] : (? [X1] : (v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) => (v1_pre_topc(sK1(X0)) & ~v2_struct_0(sK1(X0)) & m1_pre_topc(sK1(X0),X0)))),
% 55.57/7.50    introduced(choice_axiom,[])).
% 55.57/7.50  
% 55.57/7.50  fof(f59,plain,(
% 55.57/7.50    ! [X0] : ((v1_pre_topc(sK1(X0)) & ~v2_struct_0(sK1(X0)) & m1_pre_topc(sK1(X0),X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f58])).
% 55.57/7.50  
% 55.57/7.50  fof(f72,plain,(
% 55.57/7.50    ( ! [X0] : (m1_pre_topc(sK1(X0),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f59])).
% 55.57/7.50  
% 55.57/7.50  fof(f2,axiom,(
% 55.57/7.50    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f22,plain,(
% 55.57/7.50    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 55.57/7.50    inference(ennf_transformation,[],[f2])).
% 55.57/7.50  
% 55.57/7.50  fof(f23,plain,(
% 55.57/7.50    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 55.57/7.50    inference(flattening,[],[f22])).
% 55.57/7.50  
% 55.57/7.50  fof(f67,plain,(
% 55.57/7.50    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f23])).
% 55.57/7.50  
% 55.57/7.50  fof(f74,plain,(
% 55.57/7.50    ( ! [X0] : (v1_pre_topc(sK1(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f59])).
% 55.57/7.50  
% 55.57/7.50  fof(f99,plain,(
% 55.57/7.50    ~v2_struct_0(sK4)),
% 55.57/7.50    inference(cnf_transformation,[],[f65])).
% 55.57/7.50  
% 55.57/7.50  fof(f10,axiom,(
% 55.57/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f36,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 55.57/7.50    inference(ennf_transformation,[],[f10])).
% 55.57/7.50  
% 55.57/7.50  fof(f78,plain,(
% 55.57/7.50    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f36])).
% 55.57/7.50  
% 55.57/7.50  fof(f16,axiom,(
% 55.57/7.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_tex_2(X1,X0) & v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f46,plain,(
% 55.57/7.50    ! [X0] : (? [X1] : (~v1_tex_2(X1,X0) & v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f16])).
% 55.57/7.50  
% 55.57/7.50  fof(f47,plain,(
% 55.57/7.50    ! [X0] : (? [X1] : (~v1_tex_2(X1,X0) & v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(flattening,[],[f46])).
% 55.57/7.50  
% 55.57/7.50  fof(f61,plain,(
% 55.57/7.50    ! [X0] : (? [X1] : (~v1_tex_2(X1,X0) & v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) => (~v1_tex_2(sK2(X0),X0) & v1_pre_topc(sK2(X0)) & ~v2_struct_0(sK2(X0)) & m1_pre_topc(sK2(X0),X0)))),
% 55.57/7.50    introduced(choice_axiom,[])).
% 55.57/7.50  
% 55.57/7.50  fof(f62,plain,(
% 55.57/7.50    ! [X0] : ((~v1_tex_2(sK2(X0),X0) & v1_pre_topc(sK2(X0)) & ~v2_struct_0(sK2(X0)) & m1_pre_topc(sK2(X0),X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f61])).
% 55.57/7.50  
% 55.57/7.50  fof(f90,plain,(
% 55.57/7.50    ( ! [X0] : (m1_pre_topc(sK2(X0),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f62])).
% 55.57/7.50  
% 55.57/7.50  fof(f93,plain,(
% 55.57/7.50    ( ! [X0] : (~v1_tex_2(sK2(X0),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f62])).
% 55.57/7.50  
% 55.57/7.50  fof(f92,plain,(
% 55.57/7.50    ( ! [X0] : (v1_pre_topc(sK2(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f62])).
% 55.57/7.50  
% 55.57/7.50  fof(f12,axiom,(
% 55.57/7.50    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f38,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f12])).
% 55.57/7.50  
% 55.57/7.50  fof(f39,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(flattening,[],[f38])).
% 55.57/7.50  
% 55.57/7.50  fof(f81,plain,(
% 55.57/7.50    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f39])).
% 55.57/7.50  
% 55.57/7.50  fof(f73,plain,(
% 55.57/7.50    ( ! [X0] : (~v2_struct_0(sK1(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f59])).
% 55.57/7.50  
% 55.57/7.50  fof(f15,axiom,(
% 55.57/7.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f44,plain,(
% 55.57/7.50    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f15])).
% 55.57/7.50  
% 55.57/7.50  fof(f45,plain,(
% 55.57/7.50    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(flattening,[],[f44])).
% 55.57/7.50  
% 55.57/7.50  fof(f89,plain,(
% 55.57/7.50    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f45])).
% 55.57/7.50  
% 55.57/7.50  fof(f13,axiom,(
% 55.57/7.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f40,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f13])).
% 55.57/7.50  
% 55.57/7.50  fof(f41,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(flattening,[],[f40])).
% 55.57/7.50  
% 55.57/7.50  fof(f60,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(nnf_transformation,[],[f41])).
% 55.57/7.50  
% 55.57/7.50  fof(f82,plain,(
% 55.57/7.50    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f60])).
% 55.57/7.50  
% 55.57/7.50  fof(f103,plain,(
% 55.57/7.50    ( ! [X0,X1] : (u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(equality_resolution,[],[f82])).
% 55.57/7.50  
% 55.57/7.50  fof(f87,plain,(
% 55.57/7.50    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f45])).
% 55.57/7.50  
% 55.57/7.50  fof(f8,axiom,(
% 55.57/7.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 55.57/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.57/7.50  
% 55.57/7.50  fof(f32,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 55.57/7.50    inference(ennf_transformation,[],[f8])).
% 55.57/7.50  
% 55.57/7.50  fof(f33,plain,(
% 55.57/7.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 55.57/7.50    inference(flattening,[],[f32])).
% 55.57/7.50  
% 55.57/7.50  fof(f75,plain,(
% 55.57/7.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f33])).
% 55.57/7.50  
% 55.57/7.50  fof(f97,plain,(
% 55.57/7.50    ~v2_struct_0(sK3)),
% 55.57/7.50    inference(cnf_transformation,[],[f65])).
% 55.57/7.50  
% 55.57/7.50  fof(f83,plain,(
% 55.57/7.50    ( ! [X2,X0,X1] : (k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f60])).
% 55.57/7.50  
% 55.57/7.50  fof(f102,plain,(
% 55.57/7.50    ( ! [X2] : (g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X2)),u1_pre_topc(k1_tex_2(sK3,X2))) | ~m1_subset_1(X2,u1_struct_0(sK3))) )),
% 55.57/7.50    inference(cnf_transformation,[],[f65])).
% 55.57/7.50  
% 55.57/7.50  fof(f77,plain,(
% 55.57/7.50    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 55.57/7.50    inference(cnf_transformation,[],[f36])).
% 55.57/7.50  
% 55.57/7.50  cnf(c_32,negated_conjecture,
% 55.57/7.50      ( m1_pre_topc(sK4,sK3) ),
% 55.57/7.50      inference(cnf_transformation,[],[f101]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1780,negated_conjecture,
% 55.57/7.50      ( m1_pre_topc(sK4,sK3) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_32]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2460,plain,
% 55.57/7.50      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1780]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3,plain,
% 55.57/7.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 55.57/7.50      inference(cnf_transformation,[],[f69]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1801,plain,
% 55.57/7.50      ( ~ m1_pre_topc(X0_50,X1_50)
% 55.57/7.50      | ~ l1_pre_topc(X1_50)
% 55.57/7.50      | l1_pre_topc(X0_50) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_3]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2439,plain,
% 55.57/7.50      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.50      | l1_pre_topc(X1_50) != iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1801]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2850,plain,
% 55.57/7.50      ( l1_pre_topc(sK3) != iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2460,c_2439]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_35,negated_conjecture,
% 55.57/7.50      ( l1_pre_topc(sK3) ),
% 55.57/7.50      inference(cnf_transformation,[],[f98]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_38,plain,
% 55.57/7.50      ( l1_pre_topc(sK3) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3095,plain,
% 55.57/7.50      ( l1_pre_topc(sK4) = iProver_top ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_2850,c_38]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_0,plain,
% 55.57/7.50      ( m1_subset_1(sK0(X0),X0) ),
% 55.57/7.50      inference(cnf_transformation,[],[f66]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1803,plain,
% 55.57/7.50      ( m1_subset_1(sK0(X0_51),X0_51) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_0]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2437,plain,
% 55.57/7.50      ( m1_subset_1(sK0(X0_51),X0_51) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1803]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_10,plain,
% 55.57/7.50      ( ~ m1_subset_1(X0,X1)
% 55.57/7.50      | v1_xboole_0(X1)
% 55.57/7.50      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 55.57/7.50      inference(cnf_transformation,[],[f76]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1796,plain,
% 55.57/7.50      ( ~ m1_subset_1(X0_52,X0_51)
% 55.57/7.50      | v1_xboole_0(X0_51)
% 55.57/7.50      | k6_domain_1(X0_51,X0_52) = k1_tarski(X0_52) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_10]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2444,plain,
% 55.57/7.50      ( k6_domain_1(X0_51,X0_52) = k1_tarski(X0_52)
% 55.57/7.50      | m1_subset_1(X0_52,X0_51) != iProver_top
% 55.57/7.50      | v1_xboole_0(X0_51) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1796]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3668,plain,
% 55.57/7.50      ( k6_domain_1(X0_51,sK0(X0_51)) = k1_tarski(sK0(X0_51))
% 55.57/7.50      | v1_xboole_0(X0_51) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2437,c_2444]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2,plain,
% 55.57/7.50      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 55.57/7.50      inference(cnf_transformation,[],[f68]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_4,plain,
% 55.57/7.50      ( v2_struct_0(X0)
% 55.57/7.50      | ~ v1_xboole_0(u1_struct_0(X0))
% 55.57/7.50      | ~ l1_struct_0(X0) ),
% 55.57/7.50      inference(cnf_transformation,[],[f70]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_420,plain,
% 55.57/7.50      ( v2_struct_0(X0)
% 55.57/7.50      | ~ v1_xboole_0(u1_struct_0(X0))
% 55.57/7.50      | ~ l1_pre_topc(X0) ),
% 55.57/7.50      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1773,plain,
% 55.57/7.50      ( v2_struct_0(X0_50)
% 55.57/7.50      | ~ v1_xboole_0(u1_struct_0(X0_50))
% 55.57/7.50      | ~ l1_pre_topc(X0_50) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_420]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2467,plain,
% 55.57/7.50      ( v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1773]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_5602,plain,
% 55.57/7.50      ( k6_domain_1(u1_struct_0(X0_50),sK0(u1_struct_0(X0_50))) = k1_tarski(sK0(u1_struct_0(X0_50)))
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_3668,c_2467]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_40266,plain,
% 55.57/7.50      ( k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4))) = k1_tarski(sK0(u1_struct_0(sK4)))
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_3095,c_5602]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_33,negated_conjecture,
% 55.57/7.50      ( v7_struct_0(sK4) ),
% 55.57/7.50      inference(cnf_transformation,[],[f100]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1779,negated_conjecture,
% 55.57/7.50      ( v7_struct_0(sK4) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_33]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2461,plain,
% 55.57/7.50      ( v7_struct_0(sK4) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1779]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_18,plain,
% 55.57/7.50      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 55.57/7.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 55.57/7.50      | v2_struct_0(X0)
% 55.57/7.50      | ~ l1_pre_topc(X0) ),
% 55.57/7.50      inference(cnf_transformation,[],[f86]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1791,plain,
% 55.57/7.50      ( m1_pre_topc(k1_tex_2(X0_50,X0_52),X0_50)
% 55.57/7.50      | ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
% 55.57/7.50      | v2_struct_0(X0_50)
% 55.57/7.50      | ~ l1_pre_topc(X0_50) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_18]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2449,plain,
% 55.57/7.50      ( m1_pre_topc(k1_tex_2(X0_50,X0_52),X0_50) = iProver_top
% 55.57/7.50      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1791]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_28,plain,
% 55.57/7.50      ( v1_tex_2(X0,X1)
% 55.57/7.50      | ~ m1_pre_topc(X0,X1)
% 55.57/7.50      | v2_struct_0(X1)
% 55.57/7.50      | ~ l1_pre_topc(X1)
% 55.57/7.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 55.57/7.50      inference(cnf_transformation,[],[f94]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1783,plain,
% 55.57/7.50      ( v1_tex_2(X0_50,X1_50)
% 55.57/7.50      | ~ m1_pre_topc(X0_50,X1_50)
% 55.57/7.50      | v2_struct_0(X1_50)
% 55.57/7.50      | ~ l1_pre_topc(X1_50)
% 55.57/7.50      | g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = g1_pre_topc(u1_struct_0(X1_50),u1_pre_topc(X1_50)) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_28]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2457,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = g1_pre_topc(u1_struct_0(X1_50),u1_pre_topc(X1_50))
% 55.57/7.50      | v1_tex_2(X0_50,X1_50) = iProver_top
% 55.57/7.50      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X1_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1783]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_4381,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,X0_52)),u1_pre_topc(k1_tex_2(X0_50,X0_52))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
% 55.57/7.50      | v1_tex_2(k1_tex_2(X0_50,X0_52),X0_50) = iProver_top
% 55.57/7.50      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2449,c_2457]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_30,plain,
% 55.57/7.50      ( ~ v1_tex_2(k1_tex_2(X0,X1),X0)
% 55.57/7.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 55.57/7.50      | ~ v7_struct_0(X0)
% 55.57/7.50      | v2_struct_0(X0)
% 55.57/7.50      | ~ l1_pre_topc(X0) ),
% 55.57/7.50      inference(cnf_transformation,[],[f96]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1782,plain,
% 55.57/7.50      ( ~ v1_tex_2(k1_tex_2(X0_50,X0_52),X0_50)
% 55.57/7.50      | ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
% 55.57/7.50      | ~ v7_struct_0(X0_50)
% 55.57/7.50      | v2_struct_0(X0_50)
% 55.57/7.50      | ~ l1_pre_topc(X0_50) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_30]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2458,plain,
% 55.57/7.50      ( v1_tex_2(k1_tex_2(X0_50,X0_52),X0_50) != iProver_top
% 55.57/7.50      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 55.57/7.50      | v7_struct_0(X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1782]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_11959,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,X0_52)),u1_pre_topc(k1_tex_2(X0_50,X0_52))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
% 55.57/7.50      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 55.57/7.50      | v7_struct_0(X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_4381,c_2458]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_19449,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))),u1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
% 55.57/7.50      | v7_struct_0(X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2437,c_11959]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_20234,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2461,c_19449]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_8,plain,
% 55.57/7.50      ( m1_pre_topc(sK1(X0),X0) | v2_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 55.57/7.50      inference(cnf_transformation,[],[f72]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1798,plain,
% 55.57/7.50      ( m1_pre_topc(sK1(X0_50),X0_50)
% 55.57/7.50      | v2_struct_0(X0_50)
% 55.57/7.50      | ~ l1_pre_topc(X0_50) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_8]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2442,plain,
% 55.57/7.50      ( m1_pre_topc(sK1(X0_50),X0_50) = iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1798]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3090,plain,
% 55.57/7.50      ( v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | l1_pre_topc(sK1(X0_50)) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2442,c_2439]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1,plain,
% 55.57/7.50      ( ~ l1_pre_topc(X0)
% 55.57/7.50      | ~ v1_pre_topc(X0)
% 55.57/7.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 55.57/7.50      inference(cnf_transformation,[],[f67]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1802,plain,
% 55.57/7.50      ( ~ l1_pre_topc(X0_50)
% 55.57/7.50      | ~ v1_pre_topc(X0_50)
% 55.57/7.50      | g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = X0_50 ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_1]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2438,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = X0_50
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | v1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1802]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_5701,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK1(X0_50)),u1_pre_topc(sK1(X0_50))) = sK1(X0_50)
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | v1_pre_topc(sK1(X0_50)) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_3090,c_2438]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_6,plain,
% 55.57/7.50      ( v2_struct_0(X0) | ~ l1_pre_topc(X0) | v1_pre_topc(sK1(X0)) ),
% 55.57/7.50      inference(cnf_transformation,[],[f74]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1800,plain,
% 55.57/7.50      ( v2_struct_0(X0_50)
% 55.57/7.50      | ~ l1_pre_topc(X0_50)
% 55.57/7.50      | v1_pre_topc(sK1(X0_50)) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_6]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1851,plain,
% 55.57/7.50      ( v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | v1_pre_topc(sK1(X0_50)) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2809,plain,
% 55.57/7.50      ( ~ l1_pre_topc(sK1(X0_50))
% 55.57/7.50      | ~ v1_pre_topc(sK1(X0_50))
% 55.57/7.50      | g1_pre_topc(u1_struct_0(sK1(X0_50)),u1_pre_topc(sK1(X0_50))) = sK1(X0_50) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_1802]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2810,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK1(X0_50)),u1_pre_topc(sK1(X0_50))) = sK1(X0_50)
% 55.57/7.50      | l1_pre_topc(sK1(X0_50)) != iProver_top
% 55.57/7.50      | v1_pre_topc(sK1(X0_50)) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_2809]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9288,plain,
% 55.57/7.50      ( l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | g1_pre_topc(u1_struct_0(sK1(X0_50)),u1_pre_topc(sK1(X0_50))) = sK1(X0_50) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_5701,c_1851,c_2810,c_3090]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9289,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK1(X0_50)),u1_pre_topc(sK1(X0_50))) = sK1(X0_50)
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(renaming,[status(thm)],[c_9288]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9298,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK1(sK4)),u1_pre_topc(sK1(sK4))) = sK1(sK4)
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_3095,c_9289]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_34,negated_conjecture,
% 55.57/7.50      ( ~ v2_struct_0(sK4) ),
% 55.57/7.50      inference(cnf_transformation,[],[f99]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_39,plain,
% 55.57/7.50      ( v2_struct_0(sK4) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9605,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK1(sK4)),u1_pre_topc(sK1(sK4))) = sK1(sK4) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_9298,c_39]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_11,plain,
% 55.57/7.50      ( ~ m1_pre_topc(X0,X1)
% 55.57/7.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 55.57/7.50      | ~ l1_pre_topc(X1) ),
% 55.57/7.50      inference(cnf_transformation,[],[f78]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1795,plain,
% 55.57/7.50      ( ~ m1_pre_topc(X0_50,X1_50)
% 55.57/7.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)),X1_50)
% 55.57/7.50      | ~ l1_pre_topc(X1_50) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_11]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2445,plain,
% 55.57/7.50      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)),X1_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X1_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1795]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_4382,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)))) = g1_pre_topc(u1_struct_0(X1_50),u1_pre_topc(X1_50))
% 55.57/7.50      | v1_tex_2(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)),X1_50) = iProver_top
% 55.57/7.50      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X1_50) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2445,c_2457]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_12625,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1(sK4)),u1_pre_topc(sK1(sK4)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1(sK4)),u1_pre_topc(sK1(sK4))))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
% 55.57/7.50      | v1_tex_2(sK1(sK4),X0_50) = iProver_top
% 55.57/7.50      | m1_pre_topc(sK1(sK4),X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_9605,c_4382]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_12670,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = sK1(sK4)
% 55.57/7.50      | v1_tex_2(sK1(sK4),X0_50) = iProver_top
% 55.57/7.50      | m1_pre_topc(sK1(sK4),X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(light_normalisation,[status(thm)],[c_12625,c_9605]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_13683,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK1(sK4)
% 55.57/7.50      | v1_tex_2(sK1(sK4),sK4) = iProver_top
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2442,c_12670]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_27,plain,
% 55.57/7.50      ( m1_pre_topc(sK2(X0),X0) | v2_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 55.57/7.50      inference(cnf_transformation,[],[f90]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1784,plain,
% 55.57/7.50      ( m1_pre_topc(sK2(X0_50),X0_50)
% 55.57/7.50      | v2_struct_0(X0_50)
% 55.57/7.50      | ~ l1_pre_topc(X0_50) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_27]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2456,plain,
% 55.57/7.50      ( m1_pre_topc(sK2(X0_50),X0_50) = iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1784]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_4380,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
% 55.57/7.50      | v1_tex_2(sK2(X0_50),X0_50) = iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2456,c_2457]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_24,plain,
% 55.57/7.50      ( ~ v1_tex_2(sK2(X0),X0) | v2_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 55.57/7.50      inference(cnf_transformation,[],[f93]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1787,plain,
% 55.57/7.50      ( ~ v1_tex_2(sK2(X0_50),X0_50)
% 55.57/7.50      | v2_struct_0(X0_50)
% 55.57/7.50      | ~ l1_pre_topc(X0_50) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_24]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1876,plain,
% 55.57/7.50      ( v1_tex_2(sK2(X0_50),X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1787]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_10132,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_4380,c_1876]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_10142,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK2(sK4)),u1_pre_topc(sK2(sK4))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_3095,c_10132]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3645,plain,
% 55.57/7.50      ( v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | l1_pre_topc(sK2(X0_50)) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2456,c_2439]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_5709,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = sK2(X0_50)
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | v1_pre_topc(sK2(X0_50)) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_3645,c_2438]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_25,plain,
% 55.57/7.50      ( v2_struct_0(X0) | ~ l1_pre_topc(X0) | v1_pre_topc(sK2(X0)) ),
% 55.57/7.50      inference(cnf_transformation,[],[f92]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1786,plain,
% 55.57/7.50      ( v2_struct_0(X0_50)
% 55.57/7.50      | ~ l1_pre_topc(X0_50)
% 55.57/7.50      | v1_pre_topc(sK2(X0_50)) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_25]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1877,plain,
% 55.57/7.50      ( v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | v1_pre_topc(sK2(X0_50)) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1786]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2804,plain,
% 55.57/7.50      ( ~ l1_pre_topc(sK2(X0_50))
% 55.57/7.50      | ~ v1_pre_topc(sK2(X0_50))
% 55.57/7.50      | g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = sK2(X0_50) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_1802]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2805,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = sK2(X0_50)
% 55.57/7.50      | l1_pre_topc(sK2(X0_50)) != iProver_top
% 55.57/7.50      | v1_pre_topc(sK2(X0_50)) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_2804]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9448,plain,
% 55.57/7.50      ( l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = sK2(X0_50) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_5709,c_1877,c_2805,c_3645]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9449,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK2(X0_50)),u1_pre_topc(sK2(X0_50))) = sK2(X0_50)
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(renaming,[status(thm)],[c_9448]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9458,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK2(sK4)),u1_pre_topc(sK2(sK4))) = sK2(sK4)
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_3095,c_9449]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9618,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK2(sK4)),u1_pre_topc(sK2(sK4))) = sK2(sK4) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_9458,c_39]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_10207,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK2(sK4)
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top ),
% 55.57/7.50      inference(light_normalisation,[status(thm)],[c_10142,c_9618]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_11003,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK2(sK4) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_10207,c_39]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_13684,plain,
% 55.57/7.50      ( sK2(sK4) = sK1(sK4)
% 55.57/7.50      | v1_tex_2(sK1(sK4),sK4) = iProver_top
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) != iProver_top ),
% 55.57/7.50      inference(demodulation,[status(thm)],[c_13683,c_11003]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_40,plain,
% 55.57/7.50      ( v7_struct_0(sK4) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3740,plain,
% 55.57/7.50      ( m1_pre_topc(sK1(sK4),sK4)
% 55.57/7.50      | v2_struct_0(sK4)
% 55.57/7.50      | ~ l1_pre_topc(sK4) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_1798]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3741,plain,
% 55.57/7.50      ( m1_pre_topc(sK1(sK4),sK4) = iProver_top
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_3740]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_14,plain,
% 55.57/7.50      ( ~ v1_tex_2(X0,X1)
% 55.57/7.50      | ~ m1_pre_topc(X0,X1)
% 55.57/7.50      | ~ v7_struct_0(X1)
% 55.57/7.50      | v2_struct_0(X1)
% 55.57/7.50      | v2_struct_0(X0)
% 55.57/7.50      | ~ l1_pre_topc(X1) ),
% 55.57/7.50      inference(cnf_transformation,[],[f81]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1793,plain,
% 55.57/7.50      ( ~ v1_tex_2(X0_50,X1_50)
% 55.57/7.50      | ~ m1_pre_topc(X0_50,X1_50)
% 55.57/7.50      | ~ v7_struct_0(X1_50)
% 55.57/7.50      | v2_struct_0(X0_50)
% 55.57/7.50      | v2_struct_0(X1_50)
% 55.57/7.50      | ~ l1_pre_topc(X1_50) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_14]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2861,plain,
% 55.57/7.50      ( ~ v1_tex_2(X0_50,sK4)
% 55.57/7.50      | ~ m1_pre_topc(X0_50,sK4)
% 55.57/7.50      | ~ v7_struct_0(sK4)
% 55.57/7.50      | v2_struct_0(X0_50)
% 55.57/7.50      | v2_struct_0(sK4)
% 55.57/7.50      | ~ l1_pre_topc(sK4) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_1793]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_5781,plain,
% 55.57/7.50      ( ~ v1_tex_2(sK1(sK4),sK4)
% 55.57/7.50      | ~ m1_pre_topc(sK1(sK4),sK4)
% 55.57/7.50      | ~ v7_struct_0(sK4)
% 55.57/7.50      | v2_struct_0(sK1(sK4))
% 55.57/7.50      | v2_struct_0(sK4)
% 55.57/7.50      | ~ l1_pre_topc(sK4) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_2861]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_5782,plain,
% 55.57/7.50      ( v1_tex_2(sK1(sK4),sK4) != iProver_top
% 55.57/7.50      | m1_pre_topc(sK1(sK4),sK4) != iProver_top
% 55.57/7.50      | v7_struct_0(sK4) != iProver_top
% 55.57/7.50      | v2_struct_0(sK1(sK4)) = iProver_top
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_5781]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_7,plain,
% 55.57/7.50      ( v2_struct_0(X0) | ~ v2_struct_0(sK1(X0)) | ~ l1_pre_topc(X0) ),
% 55.57/7.50      inference(cnf_transformation,[],[f73]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1799,plain,
% 55.57/7.50      ( v2_struct_0(X0_50)
% 55.57/7.50      | ~ v2_struct_0(sK1(X0_50))
% 55.57/7.50      | ~ l1_pre_topc(X0_50) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_7]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9046,plain,
% 55.57/7.50      ( ~ v2_struct_0(sK1(sK4)) | v2_struct_0(sK4) | ~ l1_pre_topc(sK4) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_1799]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9047,plain,
% 55.57/7.50      ( v2_struct_0(sK1(sK4)) != iProver_top
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_9046]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_13952,plain,
% 55.57/7.50      ( sK2(sK4) = sK1(sK4) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_13684,c_38,c_39,c_40,c_2850,c_3741,c_5782,c_9047]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_13969,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK1(sK4) ),
% 55.57/7.50      inference(demodulation,[status(thm)],[c_13952,c_11003]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_4258,plain,
% 55.57/7.50      ( m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | l1_pre_topc(k1_tex_2(X0_50,X0_52)) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2449,c_2439]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_8274,plain,
% 55.57/7.50      ( v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | l1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2437,c_4258]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9200,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))),u1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))))) = k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | v1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_8274,c_2438]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2815,plain,
% 55.57/7.50      ( m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X0_50)) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_1803]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2820,plain,
% 55.57/7.50      ( m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X0_50)) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_2815]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_21,plain,
% 55.57/7.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 55.57/7.50      | v2_struct_0(X1)
% 55.57/7.50      | ~ l1_pre_topc(X1)
% 55.57/7.50      | v1_pre_topc(k1_tex_2(X1,X0)) ),
% 55.57/7.50      inference(cnf_transformation,[],[f89]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1790,plain,
% 55.57/7.50      ( ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
% 55.57/7.50      | v2_struct_0(X0_50)
% 55.57/7.50      | ~ l1_pre_topc(X0_50)
% 55.57/7.50      | v1_pre_topc(k1_tex_2(X0_50,X0_52)) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_21]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2951,plain,
% 55.57/7.50      ( ~ m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X0_50))
% 55.57/7.50      | v2_struct_0(X0_50)
% 55.57/7.50      | ~ l1_pre_topc(X0_50)
% 55.57/7.50      | v1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_1790]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2956,plain,
% 55.57/7.50      ( m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X0_50)) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | v1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_2951]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_19180,plain,
% 55.57/7.50      ( l1_pre_topc(X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))),u1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))))) = k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_9200,c_2820,c_2956]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_19181,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))),u1_pre_topc(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))))) = k1_tex_2(X0_50,sK0(u1_struct_0(X0_50)))
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(renaming,[status(thm)],[c_19180]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_19190,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK4,sK0(u1_struct_0(sK4)))
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_3095,c_19181]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_19524,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK4,sK0(u1_struct_0(sK4))) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_19190,c_39]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_20264,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))) = sK1(sK4)
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) != iProver_top ),
% 55.57/7.50      inference(light_normalisation,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_20234,c_13969,c_19524]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_20265,plain,
% 55.57/7.50      ( k1_tex_2(sK4,sK0(u1_struct_0(sK4))) = sK1(sK4)
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) != iProver_top ),
% 55.57/7.50      inference(demodulation,[status(thm)],[c_20264,c_19524]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2856,plain,
% 55.57/7.50      ( ~ v1_tex_2(k1_tex_2(sK4,X0_52),sK4)
% 55.57/7.50      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 55.57/7.50      | ~ v7_struct_0(sK4)
% 55.57/7.50      | v2_struct_0(sK4)
% 55.57/7.50      | ~ l1_pre_topc(sK4) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_1782]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3018,plain,
% 55.57/7.50      ( ~ v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),sK4)
% 55.57/7.50      | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
% 55.57/7.50      | ~ v7_struct_0(sK4)
% 55.57/7.50      | v2_struct_0(sK4)
% 55.57/7.50      | ~ l1_pre_topc(sK4) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_2856]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3020,plain,
% 55.57/7.50      ( v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),sK4) != iProver_top
% 55.57/7.50      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
% 55.57/7.50      | v7_struct_0(sK4) != iProver_top
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_3018]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3019,plain,
% 55.57/7.50      ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_2815]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3022,plain,
% 55.57/7.50      ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_3019]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_19527,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))))),u1_pre_topc(g1_pre_topc(u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))))) = g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))
% 55.57/7.50      | v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),X0_50) = iProver_top
% 55.57/7.50      | m1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_19524,c_4382]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_19567,plain,
% 55.57/7.50      ( g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50)) = k1_tex_2(sK4,sK0(u1_struct_0(sK4)))
% 55.57/7.50      | v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),X0_50) = iProver_top
% 55.57/7.50      | m1_pre_topc(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(light_normalisation,[status(thm)],[c_19527,c_19524]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_19865,plain,
% 55.57/7.50      ( k1_tex_2(sK4,sK0(u1_struct_0(sK4))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
% 55.57/7.50      | v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),sK4) = iProver_top
% 55.57/7.50      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2449,c_19567]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_19866,plain,
% 55.57/7.50      ( k1_tex_2(sK4,sK0(u1_struct_0(sK4))) = sK1(sK4)
% 55.57/7.50      | v1_tex_2(k1_tex_2(sK4,sK0(u1_struct_0(sK4))),sK4) = iProver_top
% 55.57/7.50      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK4) != iProver_top ),
% 55.57/7.50      inference(light_normalisation,[status(thm)],[c_19865,c_13969]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_20875,plain,
% 55.57/7.50      ( k1_tex_2(sK4,sK0(u1_struct_0(sK4))) = sK1(sK4) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_20265,c_38,c_39,c_40,c_2850,c_3020,c_3022,c_19866]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_17,plain,
% 55.57/7.50      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
% 55.57/7.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 55.57/7.50      | v2_struct_0(X0)
% 55.57/7.50      | v2_struct_0(k1_tex_2(X0,X1))
% 55.57/7.50      | ~ l1_pre_topc(X0)
% 55.57/7.50      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 55.57/7.50      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 55.57/7.50      inference(cnf_transformation,[],[f103]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_222,plain,
% 55.57/7.50      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 55.57/7.50      | v2_struct_0(X0)
% 55.57/7.50      | v2_struct_0(k1_tex_2(X0,X1))
% 55.57/7.50      | ~ l1_pre_topc(X0)
% 55.57/7.50      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 55.57/7.50      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_17,c_18]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_223,plain,
% 55.57/7.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 55.57/7.50      | v2_struct_0(X1)
% 55.57/7.50      | v2_struct_0(k1_tex_2(X1,X0))
% 55.57/7.50      | ~ l1_pre_topc(X1)
% 55.57/7.50      | ~ v1_pre_topc(k1_tex_2(X1,X0))
% 55.57/7.50      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 55.57/7.50      inference(renaming,[status(thm)],[c_222]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_23,plain,
% 55.57/7.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 55.57/7.50      | v2_struct_0(X1)
% 55.57/7.50      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 55.57/7.50      | ~ l1_pre_topc(X1) ),
% 55.57/7.50      inference(cnf_transformation,[],[f87]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_228,plain,
% 55.57/7.50      ( ~ l1_pre_topc(X1)
% 55.57/7.50      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 55.57/7.50      | v2_struct_0(X1)
% 55.57/7.50      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_223,c_23,c_21]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_229,plain,
% 55.57/7.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 55.57/7.50      | v2_struct_0(X1)
% 55.57/7.50      | ~ l1_pre_topc(X1)
% 55.57/7.50      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 55.57/7.50      inference(renaming,[status(thm)],[c_228]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1775,plain,
% 55.57/7.50      ( ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
% 55.57/7.50      | v2_struct_0(X0_50)
% 55.57/7.50      | ~ l1_pre_topc(X0_50)
% 55.57/7.50      | k6_domain_1(u1_struct_0(X0_50),X0_52) = u1_struct_0(k1_tex_2(X0_50,X0_52)) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_229]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2465,plain,
% 55.57/7.50      ( k6_domain_1(u1_struct_0(X0_50),X0_52) = u1_struct_0(k1_tex_2(X0_50,X0_52))
% 55.57/7.50      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_6544,plain,
% 55.57/7.50      ( k6_domain_1(u1_struct_0(X0_50),sK0(u1_struct_0(X0_50))) = u1_struct_0(k1_tex_2(X0_50,sK0(u1_struct_0(X0_50))))
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2437,c_2465]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_8088,plain,
% 55.57/7.50      ( k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4))) = u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4))))
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_3095,c_6544]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_8379,plain,
% 55.57/7.50      ( k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4))) = u1_struct_0(k1_tex_2(sK4,sK0(u1_struct_0(sK4)))) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_8088,c_39]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_20882,plain,
% 55.57/7.50      ( k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4))) = u1_struct_0(sK1(sK4)) ),
% 55.57/7.50      inference(demodulation,[status(thm)],[c_20875,c_8379]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_40449,plain,
% 55.57/7.50      ( k1_tarski(sK0(u1_struct_0(sK4))) = u1_struct_0(sK1(sK4))
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top ),
% 55.57/7.50      inference(light_normalisation,[status(thm)],[c_40266,c_20882]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_42254,plain,
% 55.57/7.50      ( k1_tarski(sK0(u1_struct_0(sK4))) = u1_struct_0(sK1(sK4)) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_40449,c_39]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9,plain,
% 55.57/7.50      ( ~ m1_pre_topc(X0,X1)
% 55.57/7.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 55.57/7.50      | m1_subset_1(X2,u1_struct_0(X1))
% 55.57/7.50      | v2_struct_0(X1)
% 55.57/7.50      | v2_struct_0(X0)
% 55.57/7.50      | ~ l1_pre_topc(X1) ),
% 55.57/7.50      inference(cnf_transformation,[],[f75]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1797,plain,
% 55.57/7.50      ( ~ m1_pre_topc(X0_50,X1_50)
% 55.57/7.50      | ~ m1_subset_1(X0_52,u1_struct_0(X0_50))
% 55.57/7.50      | m1_subset_1(X0_52,u1_struct_0(X1_50))
% 55.57/7.50      | v2_struct_0(X0_50)
% 55.57/7.50      | v2_struct_0(X1_50)
% 55.57/7.50      | ~ l1_pre_topc(X1_50) ),
% 55.57/7.50      inference(subtyping,[status(esa)],[c_9]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2443,plain,
% 55.57/7.50      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.50      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 55.57/7.50      | m1_subset_1(X0_52,u1_struct_0(X1_50)) = iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X1_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1797]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3519,plain,
% 55.57/7.50      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.50      | m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X1_50)) = iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X1_50) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2437,c_2443]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_9099,plain,
% 55.57/7.50      ( k6_domain_1(u1_struct_0(X0_50),sK0(u1_struct_0(X1_50))) = k1_tarski(sK0(u1_struct_0(X1_50)))
% 55.57/7.50      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_3519,c_2444]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_1898,plain,
% 55.57/7.50      ( v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(predicate_to_equality,[status(thm)],[c_1773]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_15532,plain,
% 55.57/7.50      ( v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.50      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 55.57/7.50      | k6_domain_1(u1_struct_0(X0_50),sK0(u1_struct_0(X1_50))) = k1_tarski(sK0(u1_struct_0(X1_50)))
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_9099,c_1898]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_15533,plain,
% 55.57/7.50      ( k6_domain_1(u1_struct_0(X0_50),sK0(u1_struct_0(X1_50))) = k1_tarski(sK0(u1_struct_0(X1_50)))
% 55.57/7.50      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 55.57/7.50      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.50      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.50      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.50      inference(renaming,[status(thm)],[c_15532]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_15543,plain,
% 55.57/7.50      ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK4))) = k1_tarski(sK0(u1_struct_0(sK4)))
% 55.57/7.50      | v2_struct_0(sK3) = iProver_top
% 55.57/7.50      | v2_struct_0(sK4) = iProver_top
% 55.57/7.50      | l1_pre_topc(sK3) != iProver_top ),
% 55.57/7.50      inference(superposition,[status(thm)],[c_2460,c_15533]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_36,negated_conjecture,
% 55.57/7.50      ( ~ v2_struct_0(sK3) ),
% 55.57/7.50      inference(cnf_transformation,[],[f97]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_116,plain,
% 55.57/7.50      ( v2_struct_0(sK3)
% 55.57/7.50      | ~ v1_xboole_0(u1_struct_0(sK3))
% 55.57/7.50      | ~ l1_struct_0(sK3) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_4]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_120,plain,
% 55.57/7.50      ( l1_struct_0(sK3) | ~ l1_pre_topc(sK3) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_2]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_2885,plain,
% 55.57/7.50      ( ~ m1_pre_topc(sK4,sK3)
% 55.57/7.50      | m1_subset_1(X0_52,u1_struct_0(sK3))
% 55.57/7.50      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 55.57/7.50      | v2_struct_0(sK3)
% 55.57/7.50      | v2_struct_0(sK4)
% 55.57/7.50      | ~ l1_pre_topc(sK3) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_1797]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3151,plain,
% 55.57/7.50      ( ~ m1_pre_topc(sK4,sK3)
% 55.57/7.50      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3))
% 55.57/7.50      | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
% 55.57/7.50      | v2_struct_0(sK3)
% 55.57/7.50      | v2_struct_0(sK4)
% 55.57/7.50      | ~ l1_pre_topc(sK3) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_2885]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_3553,plain,
% 55.57/7.50      ( ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3))
% 55.57/7.50      | v1_xboole_0(u1_struct_0(sK3))
% 55.57/7.50      | k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK4))) = k1_tarski(sK0(u1_struct_0(sK4))) ),
% 55.57/7.50      inference(instantiation,[status(thm)],[c_1796]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_15628,plain,
% 55.57/7.50      ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK4))) = k1_tarski(sK0(u1_struct_0(sK4))) ),
% 55.57/7.50      inference(global_propositional_subsumption,
% 55.57/7.50                [status(thm)],
% 55.57/7.50                [c_15543,c_36,c_35,c_34,c_32,c_116,c_120,c_3019,c_3151,
% 55.57/7.50                 c_3553]) ).
% 55.57/7.50  
% 55.57/7.50  cnf(c_16,plain,
% 55.57/7.51      ( ~ m1_pre_topc(X0,X1)
% 55.57/7.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 55.57/7.51      | v2_struct_0(X1)
% 55.57/7.51      | v2_struct_0(X0)
% 55.57/7.51      | ~ l1_pre_topc(X1)
% 55.57/7.51      | ~ v1_pre_topc(X0)
% 55.57/7.51      | k1_tex_2(X1,X2) = X0
% 55.57/7.51      | k6_domain_1(u1_struct_0(X1),X2) != u1_struct_0(X0) ),
% 55.57/7.51      inference(cnf_transformation,[],[f83]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_1792,plain,
% 55.57/7.51      ( ~ m1_pre_topc(X0_50,X1_50)
% 55.57/7.51      | ~ m1_subset_1(X0_52,u1_struct_0(X1_50))
% 55.57/7.51      | v2_struct_0(X0_50)
% 55.57/7.51      | v2_struct_0(X1_50)
% 55.57/7.51      | ~ l1_pre_topc(X1_50)
% 55.57/7.51      | ~ v1_pre_topc(X0_50)
% 55.57/7.51      | k6_domain_1(u1_struct_0(X1_50),X0_52) != u1_struct_0(X0_50)
% 55.57/7.51      | k1_tex_2(X1_50,X0_52) = X0_50 ),
% 55.57/7.51      inference(subtyping,[status(esa)],[c_16]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_2448,plain,
% 55.57/7.51      ( k6_domain_1(u1_struct_0(X0_50),X0_52) != u1_struct_0(X1_50)
% 55.57/7.51      | k1_tex_2(X0_50,X0_52) = X1_50
% 55.57/7.51      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 55.57/7.51      | m1_subset_1(X0_52,u1_struct_0(X0_50)) != iProver_top
% 55.57/7.51      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.51      | v1_pre_topc(X1_50) != iProver_top ),
% 55.57/7.51      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_15631,plain,
% 55.57/7.51      ( k1_tarski(sK0(u1_struct_0(sK4))) != u1_struct_0(X0_50)
% 55.57/7.51      | k1_tex_2(sK3,sK0(u1_struct_0(sK4))) = X0_50
% 55.57/7.51      | m1_pre_topc(X0_50,sK3) != iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) != iProver_top
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | v2_struct_0(sK3) = iProver_top
% 55.57/7.51      | l1_pre_topc(sK3) != iProver_top
% 55.57/7.51      | v1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.51      inference(superposition,[status(thm)],[c_15628,c_2448]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_37,plain,
% 55.57/7.51      ( v2_struct_0(sK3) != iProver_top ),
% 55.57/7.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_41,plain,
% 55.57/7.51      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 55.57/7.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_3153,plain,
% 55.57/7.51      ( m1_pre_topc(sK4,sK3) != iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) = iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
% 55.57/7.51      | v2_struct_0(sK3) = iProver_top
% 55.57/7.51      | v2_struct_0(sK4) = iProver_top
% 55.57/7.51      | l1_pre_topc(sK3) != iProver_top ),
% 55.57/7.51      inference(predicate_to_equality,[status(thm)],[c_3151]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_16155,plain,
% 55.57/7.51      ( m1_pre_topc(X0_50,sK3) != iProver_top
% 55.57/7.51      | k1_tex_2(sK3,sK0(u1_struct_0(sK4))) = X0_50
% 55.57/7.51      | k1_tarski(sK0(u1_struct_0(sK4))) != u1_struct_0(X0_50)
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | v1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.51      inference(global_propositional_subsumption,
% 55.57/7.51                [status(thm)],
% 55.57/7.51                [c_15631,c_37,c_38,c_39,c_41,c_3022,c_3153]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_16156,plain,
% 55.57/7.51      ( k1_tarski(sK0(u1_struct_0(sK4))) != u1_struct_0(X0_50)
% 55.57/7.51      | k1_tex_2(sK3,sK0(u1_struct_0(sK4))) = X0_50
% 55.57/7.51      | m1_pre_topc(X0_50,sK3) != iProver_top
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | v1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.51      inference(renaming,[status(thm)],[c_16155]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_42303,plain,
% 55.57/7.51      ( u1_struct_0(sK1(sK4)) != u1_struct_0(X0_50)
% 55.57/7.51      | k1_tex_2(sK3,sK0(u1_struct_0(sK4))) = X0_50
% 55.57/7.51      | m1_pre_topc(X0_50,sK3) != iProver_top
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | v1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.51      inference(demodulation,[status(thm)],[c_42254,c_16156]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_44758,plain,
% 55.57/7.51      ( k1_tex_2(sK3,sK0(u1_struct_0(sK4))) = sK1(sK4)
% 55.57/7.51      | m1_pre_topc(sK1(sK4),sK3) != iProver_top
% 55.57/7.51      | v2_struct_0(sK1(sK4)) = iProver_top
% 55.57/7.51      | v1_pre_topc(sK1(sK4)) != iProver_top ),
% 55.57/7.51      inference(equality_resolution,[status(thm)],[c_42303]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_9098,plain,
% 55.57/7.51      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.51      | m1_pre_topc(X1_50,X2_50) != iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X2_50)) = iProver_top
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.51      | v2_struct_0(X2_50) = iProver_top
% 55.57/7.51      | l1_pre_topc(X1_50) != iProver_top
% 55.57/7.51      | l1_pre_topc(X2_50) != iProver_top ),
% 55.57/7.51      inference(superposition,[status(thm)],[c_3519,c_2443]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_24172,plain,
% 55.57/7.51      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.51      | m1_pre_topc(X1_50,X2_50) != iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(X0_50)),u1_struct_0(X2_50)) = iProver_top
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.51      | v2_struct_0(X2_50) = iProver_top
% 55.57/7.51      | l1_pre_topc(X2_50) != iProver_top ),
% 55.57/7.51      inference(forward_subsumption_resolution,
% 55.57/7.51                [status(thm)],
% 55.57/7.51                [c_9098,c_2439]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_24174,plain,
% 55.57/7.51      ( m1_pre_topc(sK3,X0_50) != iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(X0_50)) = iProver_top
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | v2_struct_0(sK3) = iProver_top
% 55.57/7.51      | v2_struct_0(sK4) = iProver_top
% 55.57/7.51      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.51      inference(superposition,[status(thm)],[c_2460,c_24172]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_24422,plain,
% 55.57/7.51      ( m1_pre_topc(sK3,X0_50) != iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(X0_50)) = iProver_top
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.51      inference(global_propositional_subsumption,
% 55.57/7.51                [status(thm)],
% 55.57/7.51                [c_24174,c_37,c_39]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_24439,plain,
% 55.57/7.51      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.51      | m1_pre_topc(sK3,X0_50) != iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(X1_50)) = iProver_top
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.51      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.51      | l1_pre_topc(X1_50) != iProver_top ),
% 55.57/7.51      inference(superposition,[status(thm)],[c_24422,c_2443]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_1850,plain,
% 55.57/7.51      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.51      | l1_pre_topc(X1_50) != iProver_top
% 55.57/7.51      | l1_pre_topc(X0_50) = iProver_top ),
% 55.57/7.51      inference(predicate_to_equality,[status(thm)],[c_1801]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_25860,plain,
% 55.57/7.51      ( v2_struct_0(X1_50) = iProver_top
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(X1_50)) = iProver_top
% 55.57/7.51      | m1_pre_topc(sK3,X0_50) != iProver_top
% 55.57/7.51      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.51      | l1_pre_topc(X1_50) != iProver_top ),
% 55.57/7.51      inference(global_propositional_subsumption,
% 55.57/7.51                [status(thm)],
% 55.57/7.51                [c_24439,c_1850]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_25861,plain,
% 55.57/7.51      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.51      | m1_pre_topc(sK3,X0_50) != iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(X1_50)) = iProver_top
% 55.57/7.51      | v2_struct_0(X0_50) = iProver_top
% 55.57/7.51      | v2_struct_0(X1_50) = iProver_top
% 55.57/7.51      | l1_pre_topc(X1_50) != iProver_top ),
% 55.57/7.51      inference(renaming,[status(thm)],[c_25860]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_25870,plain,
% 55.57/7.51      ( m1_pre_topc(sK3,sK4) != iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) = iProver_top
% 55.57/7.51      | v2_struct_0(sK3) = iProver_top
% 55.57/7.51      | v2_struct_0(sK4) = iProver_top
% 55.57/7.51      | l1_pre_topc(sK3) != iProver_top ),
% 55.57/7.51      inference(superposition,[status(thm)],[c_2460,c_25861]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_25960,plain,
% 55.57/7.51      ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) = iProver_top ),
% 55.57/7.51      inference(global_propositional_subsumption,
% 55.57/7.51                [status(thm)],
% 55.57/7.51                [c_25870,c_37,c_38,c_39,c_41,c_3022,c_3153]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_25968,plain,
% 55.57/7.51      ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK4))) = u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))
% 55.57/7.51      | v2_struct_0(sK3) = iProver_top
% 55.57/7.51      | l1_pre_topc(sK3) != iProver_top ),
% 55.57/7.51      inference(superposition,[status(thm)],[c_25960,c_2465]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_26000,plain,
% 55.57/7.51      ( u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = k1_tarski(sK0(u1_struct_0(sK4)))
% 55.57/7.51      | v2_struct_0(sK3) = iProver_top
% 55.57/7.51      | l1_pre_topc(sK3) != iProver_top ),
% 55.57/7.51      inference(light_normalisation,[status(thm)],[c_25968,c_15628]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_27001,plain,
% 55.57/7.51      ( u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = k1_tarski(sK0(u1_struct_0(sK4))) ),
% 55.57/7.51      inference(global_propositional_subsumption,
% 55.57/7.51                [status(thm)],
% 55.57/7.51                [c_26000,c_37,c_38]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_31,negated_conjecture,
% 55.57/7.51      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 55.57/7.51      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X0)),u1_pre_topc(k1_tex_2(sK3,X0))) ),
% 55.57/7.51      inference(cnf_transformation,[],[f102]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_1781,negated_conjecture,
% 55.57/7.51      ( ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 55.57/7.51      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X0_52)),u1_pre_topc(k1_tex_2(sK3,X0_52))) ),
% 55.57/7.51      inference(subtyping,[status(esa)],[c_31]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_2459,plain,
% 55.57/7.51      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X0_52)),u1_pre_topc(k1_tex_2(sK3,X0_52)))
% 55.57/7.51      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
% 55.57/7.51      inference(predicate_to_equality,[status(thm)],[c_1781]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_11015,plain,
% 55.57/7.51      ( g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X0_52)),u1_pre_topc(k1_tex_2(sK3,X0_52))) != sK2(sK4)
% 55.57/7.51      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
% 55.57/7.51      inference(demodulation,[status(thm)],[c_11003,c_2459]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_13967,plain,
% 55.57/7.51      ( g1_pre_topc(u1_struct_0(k1_tex_2(sK3,X0_52)),u1_pre_topc(k1_tex_2(sK3,X0_52))) != sK1(sK4)
% 55.57/7.51      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
% 55.57/7.51      inference(demodulation,[status(thm)],[c_13952,c_11015]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_27057,plain,
% 55.57/7.51      ( g1_pre_topc(k1_tarski(sK0(u1_struct_0(sK4))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) != sK1(sK4)
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) != iProver_top ),
% 55.57/7.51      inference(superposition,[status(thm)],[c_27001,c_13967]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_28372,plain,
% 55.57/7.51      ( g1_pre_topc(k1_tarski(sK0(u1_struct_0(sK4))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) != sK1(sK4) ),
% 55.57/7.51      inference(global_propositional_subsumption,
% 55.57/7.51                [status(thm)],
% 55.57/7.51                [c_27057,c_37,c_38,c_39,c_41,c_3022,c_3153]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_25967,plain,
% 55.57/7.51      ( v2_struct_0(sK3) = iProver_top
% 55.57/7.51      | l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = iProver_top
% 55.57/7.51      | l1_pre_topc(sK3) != iProver_top ),
% 55.57/7.51      inference(superposition,[status(thm)],[c_25960,c_4258]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_3533,plain,
% 55.57/7.51      ( m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),sK3)
% 55.57/7.51      | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3))
% 55.57/7.51      | v2_struct_0(sK3)
% 55.57/7.51      | ~ l1_pre_topc(sK3) ),
% 55.57/7.51      inference(instantiation,[status(thm)],[c_1791]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_3543,plain,
% 55.57/7.51      ( m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),sK3) = iProver_top
% 55.57/7.51      | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) != iProver_top
% 55.57/7.51      | v2_struct_0(sK3) = iProver_top
% 55.57/7.51      | l1_pre_topc(sK3) != iProver_top ),
% 55.57/7.51      inference(predicate_to_equality,[status(thm)],[c_3533]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_5221,plain,
% 55.57/7.51      ( ~ m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),X0_50)
% 55.57/7.51      | ~ l1_pre_topc(X0_50)
% 55.57/7.51      | l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) ),
% 55.57/7.51      inference(instantiation,[status(thm)],[c_1801]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_5222,plain,
% 55.57/7.51      ( m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),X0_50) != iProver_top
% 55.57/7.51      | l1_pre_topc(X0_50) != iProver_top
% 55.57/7.51      | l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = iProver_top ),
% 55.57/7.51      inference(predicate_to_equality,[status(thm)],[c_5221]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_5224,plain,
% 55.57/7.51      ( m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),sK3) != iProver_top
% 55.57/7.51      | l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = iProver_top
% 55.57/7.51      | l1_pre_topc(sK3) != iProver_top ),
% 55.57/7.51      inference(instantiation,[status(thm)],[c_5222]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_26181,plain,
% 55.57/7.51      ( l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) = iProver_top ),
% 55.57/7.51      inference(global_propositional_subsumption,
% 55.57/7.51                [status(thm)],
% 55.57/7.51                [c_25967,c_37,c_38,c_39,c_41,c_3022,c_3153,c_3543,c_5224]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_26196,plain,
% 55.57/7.51      ( g1_pre_topc(u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK3,sK0(u1_struct_0(sK4)))
% 55.57/7.51      | v1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) != iProver_top ),
% 55.57/7.51      inference(superposition,[status(thm)],[c_26181,c_2438]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_3534,plain,
% 55.57/7.51      ( ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK3))
% 55.57/7.51      | v2_struct_0(sK3)
% 55.57/7.51      | ~ l1_pre_topc(sK3)
% 55.57/7.51      | v1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))) ),
% 55.57/7.51      inference(instantiation,[status(thm)],[c_1790]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_3797,plain,
% 55.57/7.51      ( ~ l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))
% 55.57/7.51      | ~ v1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))
% 55.57/7.51      | g1_pre_topc(u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK3,sK0(u1_struct_0(sK4))) ),
% 55.57/7.51      inference(instantiation,[status(thm)],[c_1802]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_5223,plain,
% 55.57/7.51      ( ~ m1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))),sK3)
% 55.57/7.51      | l1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))
% 55.57/7.51      | ~ l1_pre_topc(sK3) ),
% 55.57/7.51      inference(instantiation,[status(thm)],[c_5221]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_27780,plain,
% 55.57/7.51      ( g1_pre_topc(u1_struct_0(k1_tex_2(sK3,sK0(u1_struct_0(sK4)))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK3,sK0(u1_struct_0(sK4))) ),
% 55.57/7.51      inference(global_propositional_subsumption,
% 55.57/7.51                [status(thm)],
% 55.57/7.51                [c_26196,c_36,c_35,c_34,c_32,c_3019,c_3151,c_3534,c_3533,
% 55.57/7.51                 c_3797,c_5223]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_27782,plain,
% 55.57/7.51      ( g1_pre_topc(k1_tarski(sK0(u1_struct_0(sK4))),u1_pre_topc(k1_tex_2(sK3,sK0(u1_struct_0(sK4))))) = k1_tex_2(sK3,sK0(u1_struct_0(sK4))) ),
% 55.57/7.51      inference(light_normalisation,[status(thm)],[c_27780,c_27001]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_28374,plain,
% 55.57/7.51      ( k1_tex_2(sK3,sK0(u1_struct_0(sK4))) != sK1(sK4) ),
% 55.57/7.51      inference(light_normalisation,[status(thm)],[c_28372,c_27782]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_11059,plain,
% 55.57/7.51      ( m1_pre_topc(sK2(sK4),X0_50) = iProver_top
% 55.57/7.51      | m1_pre_topc(sK4,X0_50) != iProver_top
% 55.57/7.51      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.51      inference(superposition,[status(thm)],[c_11003,c_2445]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_13968,plain,
% 55.57/7.51      ( m1_pre_topc(sK1(sK4),X0_50) = iProver_top
% 55.57/7.51      | m1_pre_topc(sK4,X0_50) != iProver_top
% 55.57/7.51      | l1_pre_topc(X0_50) != iProver_top ),
% 55.57/7.51      inference(demodulation,[status(thm)],[c_13952,c_11059]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_14033,plain,
% 55.57/7.51      ( m1_pre_topc(sK1(sK4),sK3) = iProver_top
% 55.57/7.51      | m1_pre_topc(sK4,sK3) != iProver_top
% 55.57/7.51      | l1_pre_topc(sK3) != iProver_top ),
% 55.57/7.51      inference(instantiation,[status(thm)],[c_13968]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_12,plain,
% 55.57/7.51      ( ~ m1_pre_topc(X0,X1)
% 55.57/7.51      | ~ l1_pre_topc(X1)
% 55.57/7.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 55.57/7.51      inference(cnf_transformation,[],[f77]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_1794,plain,
% 55.57/7.51      ( ~ m1_pre_topc(X0_50,X1_50)
% 55.57/7.51      | ~ l1_pre_topc(X1_50)
% 55.57/7.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))) ),
% 55.57/7.51      inference(subtyping,[status(esa)],[c_12]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_2446,plain,
% 55.57/7.51      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 55.57/7.51      | l1_pre_topc(X1_50) != iProver_top
% 55.57/7.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_50),u1_pre_topc(X0_50))) = iProver_top ),
% 55.57/7.51      inference(predicate_to_equality,[status(thm)],[c_1794]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_3496,plain,
% 55.57/7.51      ( l1_pre_topc(sK3) != iProver_top
% 55.57/7.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 55.57/7.51      inference(superposition,[status(thm)],[c_2460,c_2446]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_2786,plain,
% 55.57/7.51      ( ~ m1_pre_topc(sK4,sK3)
% 55.57/7.51      | ~ l1_pre_topc(sK3)
% 55.57/7.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 55.57/7.51      inference(instantiation,[status(thm)],[c_1794]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_2787,plain,
% 55.57/7.51      ( m1_pre_topc(sK4,sK3) != iProver_top
% 55.57/7.51      | l1_pre_topc(sK3) != iProver_top
% 55.57/7.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 55.57/7.51      inference(predicate_to_equality,[status(thm)],[c_2786]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_3834,plain,
% 55.57/7.51      ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 55.57/7.51      inference(global_propositional_subsumption,
% 55.57/7.51                [status(thm)],
% 55.57/7.51                [c_3496,c_38,c_41,c_2787]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_11013,plain,
% 55.57/7.51      ( v1_pre_topc(sK2(sK4)) = iProver_top ),
% 55.57/7.51      inference(demodulation,[status(thm)],[c_11003,c_3834]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(c_13965,plain,
% 55.57/7.51      ( v1_pre_topc(sK1(sK4)) = iProver_top ),
% 55.57/7.51      inference(demodulation,[status(thm)],[c_13952,c_11013]) ).
% 55.57/7.51  
% 55.57/7.51  cnf(contradiction,plain,
% 55.57/7.51      ( $false ),
% 55.57/7.51      inference(minisat,
% 55.57/7.51                [status(thm)],
% 55.57/7.51                [c_44758,c_28374,c_14033,c_13965,c_9047,c_2850,c_41,c_39,
% 55.57/7.51                 c_38]) ).
% 55.57/7.51  
% 55.57/7.51  
% 55.57/7.51  % SZS output end CNFRefutation for theBenchmark.p
% 55.57/7.51  
% 55.57/7.51  ------                               Statistics
% 55.57/7.51  
% 55.57/7.51  ------ General
% 55.57/7.51  
% 55.57/7.51  abstr_ref_over_cycles:                  0
% 55.57/7.51  abstr_ref_under_cycles:                 0
% 55.57/7.51  gc_basic_clause_elim:                   0
% 55.57/7.51  forced_gc_time:                         0
% 55.57/7.51  parsing_time:                           0.01
% 55.57/7.51  unif_index_cands_time:                  0.
% 55.57/7.51  unif_index_add_time:                    0.
% 55.57/7.51  orderings_time:                         0.
% 55.57/7.51  out_proof_time:                         0.028
% 55.57/7.51  total_time:                             6.673
% 55.57/7.51  num_of_symbols:                         54
% 55.57/7.51  num_of_terms:                           32342
% 55.57/7.51  
% 55.57/7.51  ------ Preprocessing
% 55.57/7.51  
% 55.57/7.51  num_of_splits:                          0
% 55.57/7.51  num_of_split_atoms:                     0
% 55.57/7.51  num_of_reused_defs:                     0
% 55.57/7.51  num_eq_ax_congr_red:                    22
% 55.57/7.51  num_of_sem_filtered_clauses:            1
% 55.57/7.51  num_of_subtypes:                        4
% 55.57/7.51  monotx_restored_types:                  0
% 55.57/7.51  sat_num_of_epr_types:                   0
% 55.57/7.51  sat_num_of_non_cyclic_types:            0
% 55.57/7.51  sat_guarded_non_collapsed_types:        1
% 55.57/7.51  num_pure_diseq_elim:                    0
% 55.57/7.51  simp_replaced_by:                       0
% 55.57/7.51  res_preprocessed:                       171
% 55.57/7.51  prep_upred:                             0
% 55.57/7.51  prep_unflattend:                        39
% 55.57/7.51  smt_new_axioms:                         0
% 55.57/7.51  pred_elim_cands:                        9
% 55.57/7.51  pred_elim:                              2
% 55.57/7.51  pred_elim_cl:                           2
% 55.57/7.51  pred_elim_cycles:                       11
% 55.57/7.51  merged_defs:                            0
% 55.57/7.51  merged_defs_ncl:                        0
% 55.57/7.51  bin_hyper_res:                          0
% 55.57/7.51  prep_cycles:                            4
% 55.57/7.51  pred_elim_time:                         0.023
% 55.57/7.51  splitting_time:                         0.
% 55.57/7.51  sem_filter_time:                        0.
% 55.57/7.51  monotx_time:                            0.
% 55.57/7.51  subtype_inf_time:                       0.
% 55.57/7.51  
% 55.57/7.51  ------ Problem properties
% 55.57/7.51  
% 55.57/7.51  clauses:                                32
% 55.57/7.51  conjectures:                            6
% 55.57/7.51  epr:                                    7
% 55.57/7.51  horn:                                   18
% 55.57/7.51  ground:                                 5
% 55.57/7.51  unary:                                  6
% 55.57/7.51  binary:                                 1
% 55.57/7.51  lits:                                   106
% 55.57/7.51  lits_eq:                                8
% 55.57/7.51  fd_pure:                                0
% 55.57/7.51  fd_pseudo:                              0
% 55.57/7.51  fd_cond:                                0
% 55.57/7.51  fd_pseudo_cond:                         1
% 55.57/7.51  ac_symbols:                             0
% 55.57/7.51  
% 55.57/7.51  ------ Propositional Solver
% 55.57/7.51  
% 55.57/7.51  prop_solver_calls:                      29
% 55.57/7.51  prop_fast_solver_calls:                 3284
% 55.57/7.51  smt_solver_calls:                       0
% 55.57/7.51  smt_fast_solver_calls:                  0
% 55.57/7.51  prop_num_of_clauses:                    13441
% 55.57/7.51  prop_preprocess_simplified:             29569
% 55.57/7.51  prop_fo_subsumed:                       347
% 55.57/7.51  prop_solver_time:                       0.
% 55.57/7.51  smt_solver_time:                        0.
% 55.57/7.51  smt_fast_solver_time:                   0.
% 55.57/7.51  prop_fast_solver_time:                  0.
% 55.57/7.51  prop_unsat_core_time:                   0.002
% 55.57/7.51  
% 55.57/7.51  ------ QBF
% 55.57/7.51  
% 55.57/7.51  qbf_q_res:                              0
% 55.57/7.51  qbf_num_tautologies:                    0
% 55.57/7.51  qbf_prep_cycles:                        0
% 55.57/7.51  
% 55.57/7.51  ------ BMC1
% 55.57/7.51  
% 55.57/7.51  bmc1_current_bound:                     -1
% 55.57/7.51  bmc1_last_solved_bound:                 -1
% 55.57/7.51  bmc1_unsat_core_size:                   -1
% 55.57/7.51  bmc1_unsat_core_parents_size:           -1
% 55.57/7.51  bmc1_merge_next_fun:                    0
% 55.57/7.51  bmc1_unsat_core_clauses_time:           0.
% 55.57/7.51  
% 55.57/7.51  ------ Instantiation
% 55.57/7.51  
% 55.57/7.51  inst_num_of_clauses:                    3804
% 55.57/7.51  inst_num_in_passive:                    1885
% 55.57/7.51  inst_num_in_active:                     1655
% 55.57/7.51  inst_num_in_unprocessed:                265
% 55.57/7.51  inst_num_of_loops:                      1840
% 55.57/7.51  inst_num_of_learning_restarts:          0
% 55.57/7.51  inst_num_moves_active_passive:          183
% 55.57/7.51  inst_lit_activity:                      0
% 55.57/7.51  inst_lit_activity_moves:                0
% 55.57/7.51  inst_num_tautologies:                   0
% 55.57/7.51  inst_num_prop_implied:                  0
% 55.57/7.51  inst_num_existing_simplified:           0
% 55.57/7.51  inst_num_eq_res_simplified:             0
% 55.57/7.51  inst_num_child_elim:                    0
% 55.57/7.51  inst_num_of_dismatching_blockings:      3723
% 55.57/7.51  inst_num_of_non_proper_insts:           3728
% 55.57/7.51  inst_num_of_duplicates:                 0
% 55.57/7.51  inst_inst_num_from_inst_to_res:         0
% 55.57/7.51  inst_dismatching_checking_time:         0.
% 55.57/7.51  
% 55.57/7.51  ------ Resolution
% 55.57/7.51  
% 55.57/7.51  res_num_of_clauses:                     0
% 55.57/7.51  res_num_in_passive:                     0
% 55.57/7.51  res_num_in_active:                      0
% 55.57/7.51  res_num_of_loops:                       175
% 55.57/7.51  res_forward_subset_subsumed:            247
% 55.57/7.51  res_backward_subset_subsumed:           4
% 55.57/7.51  res_forward_subsumed:                   0
% 55.57/7.51  res_backward_subsumed:                  0
% 55.57/7.51  res_forward_subsumption_resolution:     3
% 55.57/7.51  res_backward_subsumption_resolution:    0
% 55.57/7.51  res_clause_to_clause_subsumption:       3796
% 55.57/7.51  res_orphan_elimination:                 0
% 55.57/7.51  res_tautology_del:                      400
% 55.57/7.51  res_num_eq_res_simplified:              0
% 55.57/7.51  res_num_sel_changes:                    0
% 55.57/7.51  res_moves_from_active_to_pass:          0
% 55.57/7.51  
% 55.57/7.51  ------ Superposition
% 55.57/7.51  
% 55.57/7.51  sup_time_total:                         0.
% 55.57/7.51  sup_time_generating:                    0.
% 55.57/7.51  sup_time_sim_full:                      0.
% 55.57/7.51  sup_time_sim_immed:                     0.
% 55.57/7.51  
% 55.57/7.51  sup_num_of_clauses:                     959
% 55.57/7.51  sup_num_in_active:                      258
% 55.57/7.51  sup_num_in_passive:                     701
% 55.57/7.51  sup_num_of_loops:                       366
% 55.57/7.51  sup_fw_superposition:                   1459
% 55.57/7.51  sup_bw_superposition:                   1314
% 55.57/7.51  sup_immediate_simplified:               582
% 55.57/7.51  sup_given_eliminated:                   0
% 55.57/7.51  comparisons_done:                       0
% 55.57/7.51  comparisons_avoided:                    0
% 55.57/7.51  
% 55.57/7.51  ------ Simplifications
% 55.57/7.51  
% 55.57/7.51  
% 55.57/7.51  sim_fw_subset_subsumed:                 62
% 55.57/7.51  sim_bw_subset_subsumed:                 7
% 55.57/7.51  sim_fw_subsumed:                        159
% 55.57/7.51  sim_bw_subsumed:                        2
% 55.57/7.51  sim_fw_subsumption_res:                 1
% 55.57/7.51  sim_bw_subsumption_res:                 0
% 55.57/7.51  sim_tautology_del:                      111
% 55.57/7.51  sim_eq_tautology_del:                   54
% 55.57/7.51  sim_eq_res_simp:                        1
% 55.57/7.51  sim_fw_demodulated:                     12
% 55.57/7.51  sim_bw_demodulated:                     107
% 55.57/7.51  sim_light_normalised:                   496
% 55.57/7.51  sim_joinable_taut:                      0
% 55.57/7.51  sim_joinable_simp:                      0
% 55.57/7.51  sim_ac_normalised:                      0
% 55.57/7.51  sim_smt_subsumption:                    0
% 55.57/7.51  
%------------------------------------------------------------------------------
