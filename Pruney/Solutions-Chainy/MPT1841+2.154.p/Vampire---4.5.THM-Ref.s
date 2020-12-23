%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:30 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 172 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  244 ( 473 expanded)
%              Number of equality atoms :   64 (  85 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f108,f141])).

fof(f141,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f139,f73])).

% (25540)Refutation not found, incomplete strategy% (25540)------------------------------
% (25540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25540)Termination reason: Refutation not found, incomplete strategy

% (25540)Memory used [KB]: 10618
% (25540)Time elapsed: 0.127 s
% (25540)------------------------------
% (25540)------------------------------
fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f55,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = sK2(X0) ),
    inference(resolution,[],[f54,f56])).

fof(f56,plain,(
    ! [X0] : v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2(X0))
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f139,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_1
    | spl3_2 ),
    inference(resolution,[],[f138,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f138,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f137,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f137,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_1
    | spl3_2 ),
    inference(superposition,[],[f136,f44])).

fof(f136,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl3_1
    | spl3_2 ),
    inference(superposition,[],[f134,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f134,plain,
    ( ! [X2] : k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)))
    | ~ spl3_1
    | spl3_2 ),
    inference(superposition,[],[f68,f117])).

fof(f117,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | ~ spl3_1
    | spl3_2 ),
    inference(forward_demodulation,[],[f116,f94])).

fof(f94,plain,
    ( k1_xboole_0 = k6_domain_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_1
  <=> k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f116,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f113,f112])).

fof(f112,plain,
    ( k1_xboole_0 != sK0
    | ~ spl3_1
    | spl3_2 ),
    inference(forward_demodulation,[],[f97,f94])).

fof(f97,plain,
    ( sK0 != k6_domain_1(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_2
  <=> sK0 = k6_domain_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f113,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f88,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f88,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,X2)
      | k1_enumset1(X1,X1,X1) = k6_domain_1(X2,X1)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f69,f54])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f62,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f68,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f57,f67,f66])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f108,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f106,f47])).

fof(f47,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f106,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f105,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f105,plain,
    ( ~ l1_struct_0(k2_yellow_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f100,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,X0)
      | ~ l1_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f78,f48])).

fof(f48,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_struct_0(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f52,f77])).

fof(f77,plain,(
    ! [X0] : k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(forward_demodulation,[],[f76,f48])).

fof(f76,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f75,f47])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f53,f51])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f100,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f42,f98])).

fof(f98,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f42,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f90,f96,f92])).

fof(f90,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(resolution,[],[f89,f41])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | sK0 = k6_domain_1(sK0,X0)
      | k1_xboole_0 = k6_domain_1(sK0,X0) ) ),
    inference(resolution,[],[f86,f54])).

fof(f86,plain,(
    ! [X0] :
      ( v1_xboole_0(k6_domain_1(sK0,X0))
      | sK0 = k6_domain_1(sK0,X0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f85,f40])).

fof(f40,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X0] :
      ( v1_xboole_0(k6_domain_1(sK0,X0))
      | sK0 = k6_domain_1(sK0,X0)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f83,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f82,f64])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f81,f40])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f50,f43])).

fof(f43,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:12:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (1242595328)
% 0.21/0.39  ipcrm: permission denied for id (1242628113)
% 0.21/0.41  ipcrm: permission denied for id (1242693659)
% 0.21/0.41  ipcrm: permission denied for id (1242726430)
% 0.21/0.42  ipcrm: permission denied for id (1242791975)
% 0.21/0.47  ipcrm: permission denied for id (1242857547)
% 0.21/0.48  ipcrm: permission denied for id (1242923092)
% 0.21/0.48  ipcrm: permission denied for id (1242988631)
% 0.21/0.49  ipcrm: permission denied for id (1243054173)
% 0.21/0.50  ipcrm: permission denied for id (1243119718)
% 0.21/0.50  ipcrm: permission denied for id (1243152489)
% 0.21/0.51  ipcrm: permission denied for id (1243185258)
% 0.21/0.51  ipcrm: permission denied for id (1243218031)
% 0.21/0.52  ipcrm: permission denied for id (1243283576)
% 0.38/0.64  % (25555)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.38/0.65  % (25547)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.38/0.65  % (25564)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.38/0.66  % (25555)Refutation not found, incomplete strategy% (25555)------------------------------
% 0.38/0.66  % (25555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (25547)Refutation not found, incomplete strategy% (25547)------------------------------
% 0.38/0.66  % (25547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (25555)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.66  
% 0.38/0.66  % (25555)Memory used [KB]: 10618
% 0.38/0.66  % (25555)Time elapsed: 0.085 s
% 0.38/0.66  % (25555)------------------------------
% 0.38/0.66  % (25555)------------------------------
% 0.38/0.66  % (25547)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.66  
% 0.38/0.66  % (25547)Memory used [KB]: 10746
% 0.38/0.66  % (25547)Time elapsed: 0.086 s
% 0.38/0.66  % (25547)------------------------------
% 0.38/0.66  % (25547)------------------------------
% 0.38/0.68  % (25564)Refutation not found, incomplete strategy% (25564)------------------------------
% 0.38/0.68  % (25564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.68  % (25564)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.68  
% 0.38/0.68  % (25564)Memory used [KB]: 6780
% 0.38/0.68  % (25564)Time elapsed: 0.092 s
% 0.38/0.68  % (25564)------------------------------
% 0.38/0.68  % (25564)------------------------------
% 0.38/0.69  % (25551)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.38/0.70  % (25545)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.38/0.70  % (25568)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.38/0.71  % (25539)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.38/0.71  % (25559)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.38/0.71  % (25559)Refutation not found, incomplete strategy% (25559)------------------------------
% 0.38/0.71  % (25559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.71  % (25559)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.71  
% 0.38/0.71  % (25559)Memory used [KB]: 1791
% 0.38/0.71  % (25559)Time elapsed: 0.117 s
% 0.38/0.71  % (25559)------------------------------
% 0.38/0.71  % (25559)------------------------------
% 0.38/0.71  % (25542)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.38/0.71  % (25541)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.38/0.71  % (25543)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.38/0.71  % (25540)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.56/0.71  % (25548)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.56/0.71  % (25541)Refutation found. Thanks to Tanya!
% 0.56/0.71  % SZS status Theorem for theBenchmark
% 0.56/0.71  % SZS output start Proof for theBenchmark
% 0.56/0.71  fof(f142,plain,(
% 0.56/0.71    $false),
% 0.56/0.71    inference(avatar_sat_refutation,[],[f99,f108,f141])).
% 0.56/0.71  fof(f141,plain,(
% 0.56/0.71    ~spl3_1 | spl3_2),
% 0.56/0.71    inference(avatar_contradiction_clause,[],[f140])).
% 0.56/0.71  fof(f140,plain,(
% 0.56/0.71    $false | (~spl3_1 | spl3_2)),
% 0.56/0.71    inference(subsumption_resolution,[],[f139,f73])).
% 0.56/0.71  % (25540)Refutation not found, incomplete strategy% (25540)------------------------------
% 0.56/0.71  % (25540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.56/0.71  % (25540)Termination reason: Refutation not found, incomplete strategy
% 0.56/0.71  
% 0.56/0.71  % (25540)Memory used [KB]: 10618
% 0.56/0.71  % (25540)Time elapsed: 0.127 s
% 0.56/0.71  % (25540)------------------------------
% 0.56/0.71  % (25540)------------------------------
% 0.56/0.71  fof(f73,plain,(
% 0.56/0.71    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.56/0.71    inference(forward_demodulation,[],[f55,f70])).
% 0.56/0.71  fof(f70,plain,(
% 0.56/0.71    ( ! [X0] : (k1_xboole_0 = sK2(X0)) )),
% 0.56/0.71    inference(resolution,[],[f54,f56])).
% 0.56/0.71  fof(f56,plain,(
% 0.56/0.71    ( ! [X0] : (v1_xboole_0(sK2(X0))) )),
% 0.56/0.71    inference(cnf_transformation,[],[f38])).
% 0.56/0.71  fof(f38,plain,(
% 0.56/0.71    ! [X0] : (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 0.56/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f37])).
% 0.56/0.71  fof(f37,plain,(
% 0.56/0.71    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0))))),
% 0.56/0.71    introduced(choice_axiom,[])).
% 0.56/0.71  fof(f9,axiom,(
% 0.56/0.71    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.56/0.71  fof(f54,plain,(
% 0.56/0.71    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.56/0.71    inference(cnf_transformation,[],[f28])).
% 0.56/0.71  fof(f28,plain,(
% 0.56/0.71    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.56/0.71    inference(ennf_transformation,[],[f1])).
% 0.56/0.71  fof(f1,axiom,(
% 0.56/0.71    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.56/0.71  fof(f55,plain,(
% 0.56/0.71    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 0.56/0.71    inference(cnf_transformation,[],[f38])).
% 0.56/0.71  fof(f139,plain,(
% 0.56/0.71    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_1 | spl3_2)),
% 0.56/0.71    inference(resolution,[],[f138,f64])).
% 0.56/0.71  fof(f64,plain,(
% 0.56/0.71    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.56/0.71    inference(cnf_transformation,[],[f39])).
% 0.56/0.71  fof(f39,plain,(
% 0.56/0.71    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.56/0.71    inference(nnf_transformation,[],[f10])).
% 0.56/0.71  fof(f10,axiom,(
% 0.56/0.71    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.56/0.71  fof(f138,plain,(
% 0.56/0.71    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_1 | spl3_2)),
% 0.56/0.71    inference(subsumption_resolution,[],[f137,f44])).
% 0.56/0.71  fof(f44,plain,(
% 0.56/0.71    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.56/0.71    inference(cnf_transformation,[],[f4])).
% 0.56/0.71  fof(f4,axiom,(
% 0.56/0.71    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.56/0.71  fof(f137,plain,(
% 0.56/0.71    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_1 | spl3_2)),
% 0.56/0.71    inference(superposition,[],[f136,f44])).
% 0.56/0.71  fof(f136,plain,(
% 0.56/0.71    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) | ~r1_tarski(X0,k1_xboole_0)) ) | (~spl3_1 | spl3_2)),
% 0.56/0.71    inference(superposition,[],[f134,f61])).
% 0.56/0.71  fof(f61,plain,(
% 0.56/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.56/0.71    inference(cnf_transformation,[],[f29])).
% 0.56/0.71  fof(f29,plain,(
% 0.56/0.71    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.56/0.71    inference(ennf_transformation,[],[f3])).
% 0.56/0.71  fof(f3,axiom,(
% 0.56/0.71    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.56/0.71  fof(f134,plain,(
% 0.56/0.71    ( ! [X2] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)))) ) | (~spl3_1 | spl3_2)),
% 0.56/0.71    inference(superposition,[],[f68,f117])).
% 0.56/0.71  fof(f117,plain,(
% 0.56/0.71    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | (~spl3_1 | spl3_2)),
% 0.56/0.71    inference(forward_demodulation,[],[f116,f94])).
% 0.56/0.71  fof(f94,plain,(
% 0.56/0.71    k1_xboole_0 = k6_domain_1(sK0,sK1) | ~spl3_1),
% 0.56/0.71    inference(avatar_component_clause,[],[f92])).
% 0.56/0.71  fof(f92,plain,(
% 0.56/0.71    spl3_1 <=> k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.56/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.56/0.71  fof(f116,plain,(
% 0.56/0.71    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | (~spl3_1 | spl3_2)),
% 0.56/0.71    inference(subsumption_resolution,[],[f113,f112])).
% 0.56/0.71  fof(f112,plain,(
% 0.56/0.71    k1_xboole_0 != sK0 | (~spl3_1 | spl3_2)),
% 0.56/0.71    inference(forward_demodulation,[],[f97,f94])).
% 0.56/0.71  fof(f97,plain,(
% 0.56/0.71    sK0 != k6_domain_1(sK0,sK1) | spl3_2),
% 0.56/0.71    inference(avatar_component_clause,[],[f96])).
% 0.56/0.71  fof(f96,plain,(
% 0.56/0.71    spl3_2 <=> sK0 = k6_domain_1(sK0,sK1)),
% 0.56/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.56/0.71  fof(f113,plain,(
% 0.56/0.71    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.56/0.71    inference(resolution,[],[f88,f41])).
% 0.56/0.71  fof(f41,plain,(
% 0.56/0.71    m1_subset_1(sK1,sK0)),
% 0.56/0.71    inference(cnf_transformation,[],[f36])).
% 0.56/0.71  fof(f36,plain,(
% 0.56/0.71    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.56/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f35,f34])).
% 0.56/0.71  fof(f34,plain,(
% 0.56/0.71    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.56/0.71    introduced(choice_axiom,[])).
% 0.56/0.71  fof(f35,plain,(
% 0.56/0.71    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.56/0.71    introduced(choice_axiom,[])).
% 0.56/0.71  fof(f22,plain,(
% 0.56/0.71    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.56/0.71    inference(flattening,[],[f21])).
% 0.56/0.71  fof(f21,plain,(
% 0.56/0.71    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.56/0.71    inference(ennf_transformation,[],[f20])).
% 0.56/0.71  fof(f20,negated_conjecture,(
% 0.56/0.71    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.56/0.71    inference(negated_conjecture,[],[f19])).
% 0.56/0.71  fof(f19,conjecture,(
% 0.56/0.71    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.56/0.71  fof(f88,plain,(
% 0.56/0.71    ( ! [X2,X1] : (~m1_subset_1(X1,X2) | k1_enumset1(X1,X1,X1) = k6_domain_1(X2,X1) | k1_xboole_0 = X2) )),
% 0.56/0.71    inference(resolution,[],[f69,f54])).
% 0.56/0.71  fof(f69,plain,(
% 0.56/0.71    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)) )),
% 0.56/0.71    inference(definition_unfolding,[],[f62,f66])).
% 0.56/0.71  fof(f66,plain,(
% 0.56/0.71    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.56/0.71    inference(definition_unfolding,[],[f45,f58])).
% 0.56/0.71  fof(f58,plain,(
% 0.56/0.71    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.56/0.71    inference(cnf_transformation,[],[f7])).
% 0.56/0.71  fof(f7,axiom,(
% 0.56/0.71    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.56/0.71  fof(f45,plain,(
% 0.56/0.71    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.56/0.71    inference(cnf_transformation,[],[f6])).
% 0.56/0.71  fof(f6,axiom,(
% 0.56/0.71    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.56/0.71  fof(f62,plain,(
% 0.56/0.71    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.56/0.71    inference(cnf_transformation,[],[f31])).
% 0.56/0.71  fof(f31,plain,(
% 0.56/0.71    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.56/0.71    inference(flattening,[],[f30])).
% 0.56/0.71  fof(f30,plain,(
% 0.56/0.71    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.56/0.71    inference(ennf_transformation,[],[f15])).
% 0.56/0.71  fof(f15,axiom,(
% 0.56/0.71    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.56/0.71  fof(f68,plain,(
% 0.56/0.71    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0))))) )),
% 0.56/0.71    inference(definition_unfolding,[],[f57,f67,f66])).
% 0.56/0.71  fof(f67,plain,(
% 0.56/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.56/0.71    inference(definition_unfolding,[],[f60,f59])).
% 0.56/0.71  fof(f59,plain,(
% 0.56/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.56/0.71    inference(cnf_transformation,[],[f2])).
% 0.56/0.71  fof(f2,axiom,(
% 0.56/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.56/0.71  fof(f60,plain,(
% 0.56/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.56/0.71    inference(cnf_transformation,[],[f5])).
% 0.56/0.71  fof(f5,axiom,(
% 0.56/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.56/0.71  fof(f57,plain,(
% 0.56/0.71    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.56/0.71    inference(cnf_transformation,[],[f8])).
% 0.56/0.71  fof(f8,axiom,(
% 0.56/0.71    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.56/0.71  fof(f108,plain,(
% 0.56/0.71    ~spl3_2),
% 0.56/0.71    inference(avatar_contradiction_clause,[],[f107])).
% 0.56/0.71  fof(f107,plain,(
% 0.56/0.71    $false | ~spl3_2),
% 0.56/0.71    inference(subsumption_resolution,[],[f106,f47])).
% 0.56/0.71  fof(f47,plain,(
% 0.56/0.71    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.56/0.71    inference(cnf_transformation,[],[f16])).
% 0.56/0.71  fof(f16,axiom,(
% 0.56/0.71    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.56/0.71  fof(f106,plain,(
% 0.56/0.71    ~l1_orders_2(k2_yellow_1(sK0)) | ~spl3_2),
% 0.56/0.71    inference(resolution,[],[f105,f51])).
% 0.56/0.71  fof(f51,plain,(
% 0.56/0.71    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.56/0.71    inference(cnf_transformation,[],[f25])).
% 0.56/0.71  fof(f25,plain,(
% 0.56/0.71    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.56/0.71    inference(ennf_transformation,[],[f14])).
% 0.56/0.71  fof(f14,axiom,(
% 0.56/0.71    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.56/0.71  fof(f105,plain,(
% 0.56/0.71    ~l1_struct_0(k2_yellow_1(sK0)) | ~spl3_2),
% 0.56/0.71    inference(resolution,[],[f100,f79])).
% 0.56/0.71  fof(f79,plain,(
% 0.56/0.71    ( ! [X0] : (~v1_subset_1(X0,X0) | ~l1_struct_0(k2_yellow_1(X0))) )),
% 0.56/0.71    inference(forward_demodulation,[],[f78,f48])).
% 0.56/0.71  fof(f48,plain,(
% 0.56/0.71    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.56/0.71    inference(cnf_transformation,[],[f17])).
% 0.56/0.71  fof(f17,axiom,(
% 0.56/0.71    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.56/0.71  fof(f78,plain,(
% 0.56/0.71    ( ! [X0] : (~v1_subset_1(X0,u1_struct_0(k2_yellow_1(X0))) | ~l1_struct_0(k2_yellow_1(X0))) )),
% 0.56/0.71    inference(superposition,[],[f52,f77])).
% 0.56/0.71  fof(f77,plain,(
% 0.56/0.71    ( ! [X0] : (k2_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.56/0.71    inference(forward_demodulation,[],[f76,f48])).
% 0.56/0.71  fof(f76,plain,(
% 0.56/0.71    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0))) )),
% 0.56/0.71    inference(resolution,[],[f75,f47])).
% 0.56/0.71  fof(f75,plain,(
% 0.56/0.71    ( ! [X0] : (~l1_orders_2(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.56/0.71    inference(resolution,[],[f53,f51])).
% 0.56/0.71  fof(f53,plain,(
% 0.56/0.71    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.56/0.71    inference(cnf_transformation,[],[f27])).
% 0.56/0.71  fof(f27,plain,(
% 0.56/0.71    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.56/0.71    inference(ennf_transformation,[],[f11])).
% 0.56/0.71  fof(f11,axiom,(
% 0.56/0.71    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.56/0.71  fof(f52,plain,(
% 0.56/0.71    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.56/0.71    inference(cnf_transformation,[],[f26])).
% 0.56/0.71  fof(f26,plain,(
% 0.56/0.71    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.56/0.71    inference(ennf_transformation,[],[f12])).
% 0.56/0.71  fof(f12,axiom,(
% 0.56/0.71    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).
% 0.56/0.71  fof(f100,plain,(
% 0.56/0.71    v1_subset_1(sK0,sK0) | ~spl3_2),
% 0.56/0.71    inference(backward_demodulation,[],[f42,f98])).
% 0.56/0.71  fof(f98,plain,(
% 0.56/0.71    sK0 = k6_domain_1(sK0,sK1) | ~spl3_2),
% 0.56/0.71    inference(avatar_component_clause,[],[f96])).
% 0.56/0.71  fof(f42,plain,(
% 0.56/0.71    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.56/0.71    inference(cnf_transformation,[],[f36])).
% 0.56/0.71  fof(f99,plain,(
% 0.56/0.71    spl3_1 | spl3_2),
% 0.56/0.71    inference(avatar_split_clause,[],[f90,f96,f92])).
% 0.56/0.71  fof(f90,plain,(
% 0.56/0.71    sK0 = k6_domain_1(sK0,sK1) | k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.56/0.71    inference(resolution,[],[f89,f41])).
% 0.56/0.71  fof(f89,plain,(
% 0.56/0.71    ( ! [X0] : (~m1_subset_1(X0,sK0) | sK0 = k6_domain_1(sK0,X0) | k1_xboole_0 = k6_domain_1(sK0,X0)) )),
% 0.56/0.71    inference(resolution,[],[f86,f54])).
% 0.56/0.71  fof(f86,plain,(
% 0.56/0.71    ( ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | sK0 = k6_domain_1(sK0,X0) | ~m1_subset_1(X0,sK0)) )),
% 0.56/0.71    inference(subsumption_resolution,[],[f85,f40])).
% 0.56/0.71  fof(f40,plain,(
% 0.56/0.71    ~v1_xboole_0(sK0)),
% 0.56/0.71    inference(cnf_transformation,[],[f36])).
% 0.56/0.71  fof(f85,plain,(
% 0.56/0.71    ( ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | sK0 = k6_domain_1(sK0,X0) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) )),
% 0.56/0.71    inference(resolution,[],[f83,f63])).
% 0.56/0.71  fof(f63,plain,(
% 0.56/0.71    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.56/0.71    inference(cnf_transformation,[],[f33])).
% 0.56/0.71  fof(f33,plain,(
% 0.56/0.71    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.56/0.71    inference(flattening,[],[f32])).
% 0.56/0.71  fof(f32,plain,(
% 0.56/0.71    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.56/0.71    inference(ennf_transformation,[],[f13])).
% 0.56/0.71  fof(f13,axiom,(
% 0.56/0.71    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.56/0.71  fof(f83,plain,(
% 0.56/0.71    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0) | sK0 = X0) )),
% 0.56/0.71    inference(resolution,[],[f82,f64])).
% 0.56/0.71  fof(f82,plain,(
% 0.56/0.71    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(X0)) )),
% 0.56/0.71    inference(subsumption_resolution,[],[f81,f40])).
% 0.56/0.71  fof(f81,plain,(
% 0.56/0.71    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 0.56/0.71    inference(resolution,[],[f50,f43])).
% 0.56/0.71  fof(f43,plain,(
% 0.56/0.71    v1_zfmisc_1(sK0)),
% 0.56/0.71    inference(cnf_transformation,[],[f36])).
% 0.56/0.71  fof(f50,plain,(
% 0.56/0.71    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.56/0.71    inference(cnf_transformation,[],[f24])).
% 0.56/0.71  fof(f24,plain,(
% 0.56/0.71    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.56/0.71    inference(flattening,[],[f23])).
% 0.56/0.71  fof(f23,plain,(
% 0.56/0.71    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.56/0.71    inference(ennf_transformation,[],[f18])).
% 0.56/0.71  fof(f18,axiom,(
% 0.56/0.71    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.56/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.56/0.71  % SZS output end Proof for theBenchmark
% 0.56/0.71  % (25541)------------------------------
% 0.56/0.71  % (25541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.56/0.71  % (25541)Termination reason: Refutation
% 0.56/0.71  
% 0.56/0.71  % (25541)Memory used [KB]: 10746
% 0.56/0.71  % (25541)Time elapsed: 0.110 s
% 0.56/0.71  % (25541)------------------------------
% 0.56/0.71  % (25541)------------------------------
% 0.56/0.71  % (25537)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.56/0.72  % (25368)Success in time 0.342 s
%------------------------------------------------------------------------------
