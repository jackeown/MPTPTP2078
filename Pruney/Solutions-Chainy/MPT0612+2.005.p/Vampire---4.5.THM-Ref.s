%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 314 expanded)
%              Number of leaves         :   21 ( 104 expanded)
%              Depth                    :   14
%              Number of atoms          :  234 ( 793 expanded)
%              Number of equality atoms :   54 ( 156 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f66,f101,f162,f192,f205,f253])).

fof(f253,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f251,f198,f64,f60,f56])).

fof(f56,plain,
    ( spl5_1
  <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f60,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f64,plain,
    ( spl5_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f198,plain,
    ( spl5_8
  <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f251,plain,
    ( k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f246,f199])).

fof(f199,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f198])).

fof(f246,plain,
    ( k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f142,f208])).

fof(f208,plain,
    ( ! [X2] : k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),X2)) = k4_xboole_0(sK2,k7_relat_1(sK2,X2))
    | ~ spl5_3 ),
    inference(resolution,[],[f146,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | k7_relat_1(sK2,k4_xboole_0(X0,X1)) = k4_xboole_0(sK2,k7_relat_1(sK2,X1)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f54,f65])).

fof(f65,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | k4_xboole_0(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f48,f40,f40])).

fof(f40,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

fof(f142,plain,
    ( ! [X0] : k7_relat_1(sK2,k1_xboole_0) = k7_relat_1(k7_relat_1(sK2,k4_xboole_0(X0,sK1)),sK0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f136,f90])).

fof(f90,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,k4_xboole_0(X0,sK1)))
    | ~ spl5_2 ),
    inference(resolution,[],[f83,f61])).

fof(f61,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f83,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k4_xboole_0(X6,X5))) ) ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,k4_xboole_0(X2,X1))),X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f71,f45])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k4_xboole_0(X2,X3))))
      | ~ r1_tarski(X1,X3) ) ),
    inference(resolution,[],[f51,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f136,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X1,X0)))
    | ~ spl5_3 ),
    inference(superposition,[],[f109,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f109,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl5_3 ),
    inference(resolution,[],[f53,f65])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f47,f41])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f205,plain,
    ( spl5_8
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f195,f190,f159,f99,f64,f198])).

fof(f99,plain,
    ( spl5_4
  <=> ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f159,plain,
    ( spl5_6
  <=> ! [X6] : k7_relat_1(k7_relat_1(sK2,X6),k1_xboole_0) = k7_relat_1(k1_xboole_0,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f190,plain,
    ( spl5_7
  <=> ! [X1,X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f195,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(superposition,[],[f191,f187])).

fof(f187,plain,
    ( ! [X2,X3] : k7_relat_1(sK2,k1_xboole_0) = k7_relat_1(k1_xboole_0,k4_xboole_0(X2,X3))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(superposition,[],[f139,f165])).

fof(f165,plain,
    ( ! [X1] : k7_relat_1(k7_relat_1(sK2,k1_xboole_0),X1) = k7_relat_1(k1_xboole_0,X1)
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(superposition,[],[f160,f144])).

fof(f144,plain,
    ( ! [X2,X3] : k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2)
    | ~ spl5_3 ),
    inference(superposition,[],[f136,f109])).

fof(f160,plain,
    ( ! [X6] : k7_relat_1(k7_relat_1(sK2,X6),k1_xboole_0) = k7_relat_1(k1_xboole_0,X6)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f139,plain,
    ( ! [X2,X1] : k7_relat_1(sK2,k1_xboole_0) = k7_relat_1(k7_relat_1(sK2,k1_xboole_0),k4_xboole_0(X1,X2))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f109,f108])).

fof(f108,plain,
    ( ! [X2,X1] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k4_xboole_0(X1,X2)))
    | ~ spl5_4 ),
    inference(resolution,[],[f100,f83])).

fof(f100,plain,
    ( ! [X1] : r1_tarski(k1_xboole_0,X1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f191,plain,
    ( ! [X0,X1] : k1_xboole_0 = k7_relat_1(k1_xboole_0,k4_xboole_0(X0,X1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( ~ spl5_3
    | spl5_7
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f186,f99,f64,f190,f64])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k4_xboole_0(X0,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f139,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f162,plain,
    ( ~ spl5_3
    | spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f153,f64,f159,f64])).

fof(f153,plain,
    ( ! [X6] :
        ( k7_relat_1(k7_relat_1(sK2,X6),k1_xboole_0) = k7_relat_1(k1_xboole_0,X6)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_3 ),
    inference(superposition,[],[f144,f36])).

fof(f101,plain,
    ( ~ spl5_2
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f95,f60,f99,f60])).

fof(f95,plain,
    ( ! [X1] :
        ( r1_tarski(k1_xboole_0,X1)
        | ~ r1_tarski(sK0,sK1) )
    | ~ spl5_2 ),
    inference(superposition,[],[f74,f90])).

fof(f66,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

% (22860)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(f62,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f50,f56])).

fof(f50,plain,(
    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f35,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (22864)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (22890)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.46  % (22874)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (22872)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (22887)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (22883)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (22880)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (22872)Refutation not found, incomplete strategy% (22872)------------------------------
% 0.21/0.51  % (22872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22872)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22872)Memory used [KB]: 10618
% 0.21/0.51  % (22872)Time elapsed: 0.092 s
% 0.21/0.51  % (22872)------------------------------
% 0.21/0.51  % (22872)------------------------------
% 0.21/0.51  % (22875)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (22883)Refutation not found, incomplete strategy% (22883)------------------------------
% 0.21/0.51  % (22883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22862)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (22871)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (22867)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (22883)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22871)Refutation not found, incomplete strategy% (22871)------------------------------
% 0.21/0.52  % (22871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22883)Memory used [KB]: 10618
% 0.21/0.52  % (22871)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22871)Memory used [KB]: 10618
% 0.21/0.52  % (22871)Time elapsed: 0.107 s
% 0.21/0.52  % (22871)------------------------------
% 0.21/0.52  % (22871)------------------------------
% 0.21/0.52  % (22883)Time elapsed: 0.051 s
% 0.21/0.52  % (22883)------------------------------
% 0.21/0.52  % (22883)------------------------------
% 0.21/0.52  % (22880)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f58,f62,f66,f101,f162,f192,f205,f253])).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f251,f198,f64,f60,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    spl5_1 <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    spl5_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    spl5_3 <=> v1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    spl5_8 <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) | (~spl5_2 | ~spl5_3 | ~spl5_8)),
% 0.21/0.52    inference(forward_demodulation,[],[f246,f199])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) | ~spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f198])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) = k7_relat_1(sK2,k1_xboole_0) | (~spl5_2 | ~spl5_3)),
% 0.21/0.52    inference(superposition,[],[f142,f208])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ( ! [X2] : (k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),X2)) = k4_xboole_0(sK2,k7_relat_1(sK2,X2))) ) | ~spl5_3),
% 0.21/0.52    inference(resolution,[],[f146,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f46,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK2),X0) | k7_relat_1(sK2,k4_xboole_0(X0,X1)) = k4_xboole_0(sK2,k7_relat_1(sK2,X1))) ) | ~spl5_3),
% 0.21/0.52    inference(resolution,[],[f54,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f64])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | k4_xboole_0(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f48,f40,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK2,k1_xboole_0) = k7_relat_1(k7_relat_1(sK2,k4_xboole_0(X0,sK1)),sK0)) ) | (~spl5_2 | ~spl5_3)),
% 0.21/0.52    inference(superposition,[],[f136,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,k4_xboole_0(X0,sK1)))) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f83,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    r1_tarski(sK0,sK1) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f60])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X6,X4,X5] : (~r1_tarski(X4,X5) | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k4_xboole_0(X6,X5)))) )),
% 0.21/0.52    inference(resolution,[],[f74,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,k4_xboole_0(X2,X1))),X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f71,f45])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k4_xboole_0(X2,X3)))) | ~r1_tarski(X1,X3)) )),
% 0.21/0.52    inference(resolution,[],[f51,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f43,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X1,X0)))) ) | ~spl5_3),
% 0.21/0.52    inference(superposition,[],[f109,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl5_3),
% 0.21/0.52    inference(resolution,[],[f53,f65])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f47,f41])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    spl5_8 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f195,f190,f159,f99,f64,f198])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl5_4 <=> ! [X1] : r1_tarski(k1_xboole_0,X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    spl5_6 <=> ! [X6] : k7_relat_1(k7_relat_1(sK2,X6),k1_xboole_0) = k7_relat_1(k1_xboole_0,X6)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    spl5_7 <=> ! [X1,X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,k4_xboole_0(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.21/0.52    inference(superposition,[],[f191,f187])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k7_relat_1(sK2,k1_xboole_0) = k7_relat_1(k1_xboole_0,k4_xboole_0(X2,X3))) ) | (~spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.21/0.52    inference(superposition,[],[f139,f165])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ( ! [X1] : (k7_relat_1(k7_relat_1(sK2,k1_xboole_0),X1) = k7_relat_1(k1_xboole_0,X1)) ) | (~spl5_3 | ~spl5_6)),
% 0.21/0.52    inference(superposition,[],[f160,f144])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2)) ) | ~spl5_3),
% 0.21/0.52    inference(superposition,[],[f136,f109])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ( ! [X6] : (k7_relat_1(k7_relat_1(sK2,X6),k1_xboole_0) = k7_relat_1(k1_xboole_0,X6)) ) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f159])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k7_relat_1(sK2,k1_xboole_0) = k7_relat_1(k7_relat_1(sK2,k1_xboole_0),k4_xboole_0(X1,X2))) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.52    inference(superposition,[],[f109,f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k4_xboole_0(X1,X2)))) ) | ~spl5_4),
% 0.21/0.52    inference(resolution,[],[f100,f83])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) ) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f99])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,k4_xboole_0(X0,X1))) ) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f190])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ~spl5_3 | spl5_7 | ~spl5_3 | ~spl5_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f186,f99,f64,f190,f64])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,k4_xboole_0(X0,X1)) | ~v1_relat_1(sK2)) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.52    inference(superposition,[],[f139,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ~spl5_3 | spl5_6 | ~spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f153,f64,f159,f64])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ( ! [X6] : (k7_relat_1(k7_relat_1(sK2,X6),k1_xboole_0) = k7_relat_1(k1_xboole_0,X6) | ~v1_relat_1(sK2)) ) | ~spl5_3),
% 0.21/0.52    inference(superposition,[],[f144,f36])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ~spl5_2 | spl5_4 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f95,f60,f99,f60])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(k1_xboole_0,X1) | ~r1_tarski(sK0,sK1)) ) | ~spl5_2),
% 0.21/0.52    inference(superposition,[],[f74,f90])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f64])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  % (22860)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f60])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    r1_tarski(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ~spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f50,f56])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.21/0.52    inference(definition_unfolding,[],[f35,f40])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22880)------------------------------
% 0.21/0.52  % (22880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22880)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22880)Memory used [KB]: 10874
% 0.21/0.52  % (22880)Time elapsed: 0.106 s
% 0.21/0.52  % (22880)------------------------------
% 0.21/0.52  % (22880)------------------------------
% 0.21/0.53  % (22856)Success in time 0.165 s
%------------------------------------------------------------------------------
