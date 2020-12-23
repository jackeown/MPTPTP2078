%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 239 expanded)
%              Number of leaves         :   23 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  307 ( 811 expanded)
%              Number of equality atoms :   72 ( 131 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f149,f165,f170,f185])).

fof(f185,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f183,f53])).

fof(f53,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f183,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f182,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f182,plain,
    ( ~ l1_struct_0(k2_yellow_1(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f171,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,X0)
      | ~ l1_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f88,f54])).

fof(f54,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_struct_0(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f58,f87])).

fof(f87,plain,(
    ! [X0] : k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(forward_demodulation,[],[f86,f54])).

fof(f86,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f85,f53])).

fof(f85,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f59,f57])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f171,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f49,f136])).

fof(f136,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_4
  <=> sK0 = k6_domain_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f49,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f170,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl5_6 ),
    inference(subsumption_resolution,[],[f168,f48])).

fof(f48,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f168,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl5_6 ),
    inference(subsumption_resolution,[],[f167,f47])).

fof(f47,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f167,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1,sK0)
    | spl5_6 ),
    inference(resolution,[],[f164,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f164,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl5_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f165,plain,
    ( spl5_4
    | ~ spl5_6
    | spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f160,f138,f112,f162,f134])).

fof(f112,plain,
    ( spl5_1
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f138,plain,
    ( spl5_5
  <=> sK1 = sK3(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f160,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k6_domain_1(sK0,sK1)
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f156,f113])).

fof(f113,plain,
    ( ~ v1_xboole_0(k6_domain_1(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f156,plain,
    ( ~ r2_hidden(sK1,sK0)
    | v1_xboole_0(k6_domain_1(sK0,sK1))
    | sK0 = k6_domain_1(sK0,sK1)
    | ~ spl5_5 ),
    inference(superposition,[],[f103,f140])).

fof(f140,plain,
    ( sK1 = sK3(k6_domain_1(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,sK0),sK0)
      | v1_xboole_0(X0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f99,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f99,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f98,f47])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f56,f50])).

fof(f50,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f149,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl5_1 ),
    inference(resolution,[],[f143,f105])).

fof(f105,plain,(
    r2_hidden(sK1,k6_domain_1(sK0,sK1)) ),
    inference(superposition,[],[f82,f102])).

fof(f102,plain,(
    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f100,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

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
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f143,plain,
    ( ! [X1] : ~ r2_hidden(X1,k6_domain_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f114,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

% (11553)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f114,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f141,plain,
    ( spl5_1
    | spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f131,f138,f134,f112])).

fof(f131,plain,
    ( sK1 = sK3(k6_domain_1(sK0,sK1),sK0)
    | sK0 = k6_domain_1(sK0,sK1)
    | v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(resolution,[],[f110,f99])).

fof(f110,plain,(
    ! [X3] :
      ( r1_tarski(k6_domain_1(sK0,sK1),X3)
      | sK1 = sK3(k6_domain_1(sK0,sK1),X3) ) ),
    inference(resolution,[],[f104,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_domain_1(sK0,sK1))
      | sK1 = X0 ) ),
    inference(superposition,[],[f83,f102])).

fof(f83,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f75])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:47:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (11548)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (11533)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (11540)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (11530)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (11528)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (11531)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (11527)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (11529)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (11525)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (11528)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f141,f149,f165,f170,f185])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    ~spl5_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f184])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    $false | ~spl5_4),
% 0.22/0.54    inference(subsumption_resolution,[],[f183,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    ~l1_orders_2(k2_yellow_1(sK0)) | ~spl5_4),
% 0.22/0.54    inference(resolution,[],[f182,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    ~l1_struct_0(k2_yellow_1(sK0)) | ~spl5_4),
% 0.22/0.54    inference(resolution,[],[f171,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_subset_1(X0,X0) | ~l1_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f88,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_subset_1(X0,u1_struct_0(k2_yellow_1(X0))) | ~l1_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(superposition,[],[f58,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0] : (k2_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.54    inference(forward_demodulation,[],[f86,f54])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(resolution,[],[f85,f53])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_orders_2(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f59,f57])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    v1_subset_1(sK0,sK0) | ~spl5_4),
% 0.22/0.54    inference(backward_demodulation,[],[f49,f136])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    sK0 = k6_domain_1(sK0,sK1) | ~spl5_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f134])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl5_4 <=> sK0 = k6_domain_1(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f32,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.54    inference(negated_conjecture,[],[f16])).
% 0.22/0.54  fof(f16,conjecture,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    spl5_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f169])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    $false | spl5_6),
% 0.22/0.54    inference(subsumption_resolution,[],[f168,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    m1_subset_1(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,sK0) | spl5_6),
% 0.22/0.54    inference(subsumption_resolution,[],[f167,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ~v1_xboole_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    v1_xboole_0(sK0) | ~m1_subset_1(sK1,sK0) | spl5_6),
% 0.22/0.54    inference(resolution,[],[f164,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK0) | spl5_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f162])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    spl5_6 <=> r2_hidden(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    spl5_4 | ~spl5_6 | spl5_1 | ~spl5_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f160,f138,f112,f162,f134])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    spl5_1 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    spl5_5 <=> sK1 = sK3(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK0) | sK0 = k6_domain_1(sK0,sK1) | (spl5_1 | ~spl5_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f156,f113])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ~v1_xboole_0(k6_domain_1(sK0,sK1)) | spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f112])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK0) | v1_xboole_0(k6_domain_1(sK0,sK1)) | sK0 = k6_domain_1(sK0,sK1) | ~spl5_5),
% 0.22/0.54    inference(superposition,[],[f103,f140])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    sK1 = sK3(k6_domain_1(sK0,sK1),sK0) | ~spl5_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f138])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(sK3(X0,sK0),sK0) | v1_xboole_0(X0) | sK0 = X0) )),
% 0.22/0.54    inference(resolution,[],[f99,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f98,f47])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f56,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    v1_zfmisc_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    ~spl5_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f146])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    $false | ~spl5_1),
% 0.22/0.54    inference(resolution,[],[f143,f105])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    r2_hidden(sK1,k6_domain_1(sK0,sK1))),
% 0.22/0.54    inference(superposition,[],[f82,f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f100,f47])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | v1_xboole_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f76,f48])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f65,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f51,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 0.22/0.54    inference(equality_resolution,[],[f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 0.22/0.54    inference(equality_resolution,[],[f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f70,f75])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(rectify,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X1] : (~r2_hidden(X1,k6_domain_1(sK0,sK1))) ) | ~spl5_1),
% 0.22/0.54    inference(resolution,[],[f114,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(rectify,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.54  % (11553)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f112])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    spl5_1 | spl5_4 | spl5_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f131,f138,f134,f112])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    sK1 = sK3(k6_domain_1(sK0,sK1),sK0) | sK0 = k6_domain_1(sK0,sK1) | v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.22/0.54    inference(resolution,[],[f110,f99])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X3] : (r1_tarski(k6_domain_1(sK0,sK1),X3) | sK1 = sK3(k6_domain_1(sK0,sK1),X3)) )),
% 0.22/0.54    inference(resolution,[],[f104,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k6_domain_1(sK0,sK1)) | sK1 = X0) )),
% 0.22/0.54    inference(superposition,[],[f83,f102])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_enumset1(X0,X0,X0)) | X0 = X3) )),
% 0.22/0.54    inference(equality_resolution,[],[f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f69,f75])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (11528)------------------------------
% 0.22/0.54  % (11528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11528)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (11528)Memory used [KB]: 10746
% 0.22/0.54  % (11528)Time elapsed: 0.126 s
% 0.22/0.54  % (11528)------------------------------
% 0.22/0.54  % (11528)------------------------------
% 0.22/0.54  % (11524)Success in time 0.178 s
%------------------------------------------------------------------------------
