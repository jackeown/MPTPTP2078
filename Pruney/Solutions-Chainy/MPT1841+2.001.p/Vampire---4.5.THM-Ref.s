%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:08 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 149 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  240 ( 473 expanded)
%              Number of equality atoms :   62 (  67 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f548,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f345,f544])).

fof(f544,plain,(
    ! [X6] : ~ v1_subset_1(X6,X6) ),
    inference(subsumption_resolution,[],[f534,f120])).

fof(f120,plain,(
    ! [X0] : l1_struct_0(g1_pre_topc(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f92,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f92,plain,(
    ! [X0] : l1_pre_topc(g1_pre_topc(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f53,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f534,plain,(
    ! [X6] :
      ( ~ v1_subset_1(X6,X6)
      | ~ l1_struct_0(g1_pre_topc(X6,k1_xboole_0)) ) ),
    inference(superposition,[],[f89,f465])).

fof(f465,plain,(
    ! [X0] : u1_struct_0(g1_pre_topc(X0,k1_xboole_0)) = X0 ),
    inference(unit_resulting_resolution,[],[f53,f119,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f119,plain,(
    ! [X0] : g1_pre_topc(X0,k1_xboole_0) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k1_xboole_0)),u1_pre_topc(g1_pre_topc(X0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f91,f92,f59])).

fof(f59,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f91,plain,(
    ! [X0] : v1_pre_topc(g1_pre_topc(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f53,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f57,f58])).

fof(f58,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f345,plain,(
    v1_subset_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f51,f257])).

fof(f257,plain,(
    sK0 = k6_domain_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f52,f49,f133,f128,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f128,plain,(
    r1_tarski(k6_domain_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f94,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f94,plain,(
    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f49,f50,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f50,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f133,plain,(
    ~ v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(superposition,[],[f86,f95])).

fof(f95,plain,(
    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f49,f50,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f67,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f62])).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f86,plain,(
    ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f82,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f82,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f49,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (806453252)
% 0.21/0.39  ipcrm: permission denied for id (806518808)
% 0.21/0.40  ipcrm: permission denied for id (806551579)
% 0.21/0.40  ipcrm: permission denied for id (806584348)
% 0.21/0.40  ipcrm: permission denied for id (806617122)
% 0.21/0.42  ipcrm: permission denied for id (806649905)
% 0.21/0.44  ipcrm: permission denied for id (806715466)
% 0.21/0.44  ipcrm: permission denied for id (806813776)
% 0.21/0.44  ipcrm: permission denied for id (806846546)
% 0.21/0.45  ipcrm: permission denied for id (806879316)
% 0.21/0.45  ipcrm: permission denied for id (806912089)
% 0.21/0.47  ipcrm: permission denied for id (807043184)
% 0.88/0.59  % (6927)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.88/0.61  % (6927)Refutation found. Thanks to Tanya!
% 0.88/0.61  % SZS status Theorem for theBenchmark
% 0.88/0.61  % (6948)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.88/0.62  % (6926)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.88/0.62  % (6935)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.88/0.62  % (6939)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.88/0.62  % (6952)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.88/0.63  % SZS output start Proof for theBenchmark
% 0.88/0.63  fof(f548,plain,(
% 0.88/0.63    $false),
% 0.88/0.63    inference(unit_resulting_resolution,[],[f345,f544])).
% 0.88/0.63  fof(f544,plain,(
% 0.88/0.63    ( ! [X6] : (~v1_subset_1(X6,X6)) )),
% 0.88/0.63    inference(subsumption_resolution,[],[f534,f120])).
% 0.88/0.63  fof(f120,plain,(
% 0.88/0.63    ( ! [X0] : (l1_struct_0(g1_pre_topc(X0,k1_xboole_0))) )),
% 0.88/0.63    inference(unit_resulting_resolution,[],[f92,f56])).
% 0.88/0.63  fof(f56,plain,(
% 0.88/0.63    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f24])).
% 0.88/0.63  fof(f24,plain,(
% 0.88/0.63    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.88/0.63    inference(ennf_transformation,[],[f11])).
% 0.88/0.63  fof(f11,axiom,(
% 0.88/0.63    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.88/0.63  fof(f92,plain,(
% 0.88/0.63    ( ! [X0] : (l1_pre_topc(g1_pre_topc(X0,k1_xboole_0))) )),
% 0.88/0.63    inference(unit_resulting_resolution,[],[f53,f64])).
% 0.88/0.63  fof(f64,plain,(
% 0.88/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.88/0.63    inference(cnf_transformation,[],[f29])).
% 0.88/0.63  fof(f29,plain,(
% 0.88/0.63    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.88/0.63    inference(ennf_transformation,[],[f10])).
% 0.88/0.63  fof(f10,axiom,(
% 0.88/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.88/0.63  fof(f53,plain,(
% 0.88/0.63    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.88/0.63    inference(cnf_transformation,[],[f5])).
% 0.88/0.63  fof(f5,axiom,(
% 0.88/0.63    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.88/0.63  fof(f534,plain,(
% 0.88/0.63    ( ! [X6] : (~v1_subset_1(X6,X6) | ~l1_struct_0(g1_pre_topc(X6,k1_xboole_0))) )),
% 0.88/0.63    inference(superposition,[],[f89,f465])).
% 0.88/0.63  fof(f465,plain,(
% 0.88/0.63    ( ! [X0] : (u1_struct_0(g1_pre_topc(X0,k1_xboole_0)) = X0) )),
% 0.88/0.63    inference(unit_resulting_resolution,[],[f53,f119,f65])).
% 0.88/0.63  fof(f65,plain,(
% 0.88/0.63    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.88/0.63    inference(cnf_transformation,[],[f30])).
% 0.88/0.63  fof(f30,plain,(
% 0.88/0.63    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.88/0.63    inference(ennf_transformation,[],[f13])).
% 0.88/0.63  fof(f13,axiom,(
% 0.88/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.88/0.63  fof(f119,plain,(
% 0.88/0.63    ( ! [X0] : (g1_pre_topc(X0,k1_xboole_0) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k1_xboole_0)),u1_pre_topc(g1_pre_topc(X0,k1_xboole_0)))) )),
% 0.88/0.63    inference(unit_resulting_resolution,[],[f91,f92,f59])).
% 0.88/0.63  fof(f59,plain,(
% 0.88/0.63    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f28])).
% 0.88/0.63  fof(f28,plain,(
% 0.88/0.63    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.88/0.63    inference(flattening,[],[f27])).
% 0.88/0.63  fof(f27,plain,(
% 0.88/0.63    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.88/0.63    inference(ennf_transformation,[],[f8])).
% 0.88/0.63  fof(f8,axiom,(
% 0.88/0.63    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.88/0.63  fof(f91,plain,(
% 0.88/0.63    ( ! [X0] : (v1_pre_topc(g1_pre_topc(X0,k1_xboole_0))) )),
% 0.88/0.63    inference(unit_resulting_resolution,[],[f53,f63])).
% 0.88/0.63  fof(f63,plain,(
% 0.88/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.88/0.63    inference(cnf_transformation,[],[f29])).
% 0.88/0.63  fof(f89,plain,(
% 0.88/0.63    ( ! [X0] : (~v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.88/0.63    inference(duplicate_literal_removal,[],[f88])).
% 0.88/0.63  fof(f88,plain,(
% 0.88/0.63    ( ! [X0] : (~v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.88/0.63    inference(superposition,[],[f57,f58])).
% 0.88/0.63  fof(f58,plain,(
% 0.88/0.63    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f26])).
% 0.88/0.63  fof(f26,plain,(
% 0.88/0.63    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.88/0.63    inference(ennf_transformation,[],[f9])).
% 0.88/0.63  fof(f9,axiom,(
% 0.88/0.63    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.88/0.63  fof(f57,plain,(
% 0.88/0.63    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f25])).
% 0.88/0.63  fof(f25,plain,(
% 0.88/0.63    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.88/0.63    inference(ennf_transformation,[],[f12])).
% 0.88/0.63  fof(f12,axiom,(
% 0.88/0.63    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).
% 0.88/0.63  fof(f345,plain,(
% 0.88/0.63    v1_subset_1(sK0,sK0)),
% 0.88/0.63    inference(backward_demodulation,[],[f51,f257])).
% 0.88/0.63  fof(f257,plain,(
% 0.88/0.63    sK0 = k6_domain_1(sK0,sK1)),
% 0.88/0.63    inference(unit_resulting_resolution,[],[f52,f49,f133,f128,f55])).
% 0.88/0.63  fof(f55,plain,(
% 0.88/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f23])).
% 0.88/0.63  fof(f23,plain,(
% 0.88/0.63    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.88/0.63    inference(flattening,[],[f22])).
% 0.88/0.63  fof(f22,plain,(
% 0.88/0.63    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.88/0.63    inference(ennf_transformation,[],[f16])).
% 0.88/0.63  fof(f16,axiom,(
% 0.88/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.88/0.63  fof(f128,plain,(
% 0.88/0.63    r1_tarski(k6_domain_1(sK0,sK1),sK0)),
% 0.88/0.63    inference(unit_resulting_resolution,[],[f94,f73])).
% 0.88/0.63  fof(f73,plain,(
% 0.88/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f35])).
% 0.88/0.63  fof(f35,plain,(
% 0.88/0.63    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.88/0.63    inference(ennf_transformation,[],[f19])).
% 0.88/0.63  fof(f19,plain,(
% 0.88/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.88/0.63    inference(unused_predicate_definition_removal,[],[f6])).
% 0.88/0.63  fof(f6,axiom,(
% 0.88/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.88/0.63  fof(f94,plain,(
% 0.88/0.63    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.88/0.63    inference(unit_resulting_resolution,[],[f49,f50,f68])).
% 0.88/0.63  fof(f68,plain,(
% 0.88/0.63    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f34])).
% 0.88/0.63  fof(f34,plain,(
% 0.88/0.63    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.88/0.63    inference(flattening,[],[f33])).
% 0.88/0.63  fof(f33,plain,(
% 0.88/0.63    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.88/0.63    inference(ennf_transformation,[],[f14])).
% 0.88/0.63  fof(f14,axiom,(
% 0.88/0.63    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.88/0.63  fof(f50,plain,(
% 0.88/0.63    m1_subset_1(sK1,sK0)),
% 0.88/0.63    inference(cnf_transformation,[],[f40])).
% 0.88/0.63  fof(f40,plain,(
% 0.88/0.63    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.88/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f39,f38])).
% 0.88/0.63  fof(f38,plain,(
% 0.88/0.63    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.88/0.63    introduced(choice_axiom,[])).
% 0.88/0.63  fof(f39,plain,(
% 0.88/0.63    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.88/0.63    introduced(choice_axiom,[])).
% 0.88/0.63  fof(f21,plain,(
% 0.88/0.63    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.88/0.63    inference(flattening,[],[f20])).
% 0.88/0.63  fof(f20,plain,(
% 0.88/0.63    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.88/0.63    inference(ennf_transformation,[],[f18])).
% 0.88/0.63  fof(f18,negated_conjecture,(
% 0.88/0.63    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.88/0.63    inference(negated_conjecture,[],[f17])).
% 0.88/0.63  fof(f17,conjecture,(
% 0.88/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.88/0.63  fof(f133,plain,(
% 0.88/0.63    ~v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.88/0.63    inference(superposition,[],[f86,f95])).
% 0.88/0.63  fof(f95,plain,(
% 0.88/0.63    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.88/0.63    inference(unit_resulting_resolution,[],[f49,f50,f76])).
% 0.88/0.63  fof(f76,plain,(
% 0.88/0.63    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.88/0.63    inference(definition_unfolding,[],[f67,f75])).
% 0.88/0.63  fof(f75,plain,(
% 0.88/0.63    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.88/0.63    inference(definition_unfolding,[],[f54,f62])).
% 0.88/0.63  fof(f62,plain,(
% 0.88/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f4])).
% 0.88/0.63  fof(f4,axiom,(
% 0.88/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.88/0.63  fof(f54,plain,(
% 0.88/0.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f3])).
% 0.88/0.63  fof(f3,axiom,(
% 0.88/0.63    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.88/0.63  fof(f67,plain,(
% 0.88/0.63    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f32])).
% 0.88/0.63  fof(f32,plain,(
% 0.88/0.63    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.88/0.63    inference(flattening,[],[f31])).
% 0.88/0.63  fof(f31,plain,(
% 0.88/0.63    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.88/0.63    inference(ennf_transformation,[],[f15])).
% 0.88/0.63  fof(f15,axiom,(
% 0.88/0.63    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.88/0.63  fof(f86,plain,(
% 0.88/0.63    ( ! [X0] : (~v1_xboole_0(k1_enumset1(X0,X0,X0))) )),
% 0.88/0.63    inference(unit_resulting_resolution,[],[f82,f60])).
% 0.88/0.63  fof(f60,plain,(
% 0.88/0.63    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f44])).
% 0.88/0.63  fof(f44,plain,(
% 0.88/0.63    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.88/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 0.88/0.63  fof(f43,plain,(
% 0.88/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.88/0.63    introduced(choice_axiom,[])).
% 0.88/0.63  fof(f42,plain,(
% 0.88/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.88/0.63    inference(rectify,[],[f41])).
% 0.88/0.63  fof(f41,plain,(
% 0.88/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.88/0.63    inference(nnf_transformation,[],[f1])).
% 0.88/0.63  fof(f1,axiom,(
% 0.88/0.63    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.88/0.63  fof(f82,plain,(
% 0.88/0.63    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 0.88/0.63    inference(equality_resolution,[],[f81])).
% 0.88/0.63  fof(f81,plain,(
% 0.88/0.63    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 0.88/0.63    inference(equality_resolution,[],[f79])).
% 0.88/0.63  fof(f79,plain,(
% 0.88/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 0.88/0.63    inference(definition_unfolding,[],[f70,f75])).
% 0.88/0.63  fof(f70,plain,(
% 0.88/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.88/0.63    inference(cnf_transformation,[],[f48])).
% 0.88/0.63  fof(f48,plain,(
% 0.88/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.88/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 0.88/0.63  fof(f47,plain,(
% 0.88/0.63    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.88/0.63    introduced(choice_axiom,[])).
% 0.88/0.63  fof(f46,plain,(
% 0.88/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.88/0.63    inference(rectify,[],[f45])).
% 0.88/0.63  fof(f45,plain,(
% 0.88/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.88/0.63    inference(nnf_transformation,[],[f2])).
% 0.88/0.63  fof(f2,axiom,(
% 0.88/0.63    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.88/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.88/0.63  fof(f49,plain,(
% 0.88/0.63    ~v1_xboole_0(sK0)),
% 0.88/0.63    inference(cnf_transformation,[],[f40])).
% 0.88/0.63  fof(f52,plain,(
% 0.88/0.63    v1_zfmisc_1(sK0)),
% 0.88/0.63    inference(cnf_transformation,[],[f40])).
% 0.88/0.63  fof(f51,plain,(
% 0.88/0.63    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.88/0.63    inference(cnf_transformation,[],[f40])).
% 0.88/0.63  % SZS output end Proof for theBenchmark
% 0.88/0.63  % (6927)------------------------------
% 0.88/0.63  % (6927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.88/0.63  % (6927)Termination reason: Refutation
% 0.88/0.63  
% 0.88/0.63  % (6927)Memory used [KB]: 1918
% 0.88/0.63  % (6927)Time elapsed: 0.089 s
% 0.88/0.63  % (6927)------------------------------
% 0.88/0.63  % (6927)------------------------------
% 0.88/0.63  % (6931)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.88/0.63  % (6776)Success in time 0.269 s
%------------------------------------------------------------------------------
