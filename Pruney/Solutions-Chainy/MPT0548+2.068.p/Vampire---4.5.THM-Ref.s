%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 108 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :  208 ( 270 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f53,f59,f64,f68,f72,f76,f82,f89,f157,f163,f176])).

fof(f176,plain,
    ( spl4_5
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl4_5
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f63,f169])).

fof(f169,plain,
    ( ! [X3] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(resolution,[],[f162,f71])).

fof(f71,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_7
  <=> ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f162,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl4_22
  <=> ! [X1,X0] : ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f63,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_5
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f163,plain,
    ( spl4_22
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f159,f155,f87,f56,f161])).

fof(f56,plain,
    ( spl4_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f87,plain,
    ( spl4_10
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f155,plain,
    ( spl4_21
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f159,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f158,f58])).

fof(f58,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_10
    | ~ spl4_21 ),
    inference(resolution,[],[f156,f88])).

fof(f88,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f36,f155])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f89,plain,
    ( spl4_10
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f85,f80,f70,f87])).

fof(f80,plain,
    ( spl4_9
  <=> ! [X1,X0] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f85,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f81,f83])).

fof(f83,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f81,f71])).

fof(f81,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,
    ( spl4_9
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f78,f74,f66,f46,f80])).

fof(f46,plain,
    ( spl4_2
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f66,plain,
    ( spl4_6
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f74,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f78,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1))
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f77,f67])).

fof(f67,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f77,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f72,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f68,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f64,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).

fof(f16,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f59,plain,
    ( spl4_4
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f54,f50,f42,f56])).

fof(f42,plain,
    ( spl4_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f50,plain,
    ( spl4_3
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f54,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f43,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f43,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f53,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f48,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f46])).

fof(f29,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f44,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f28,f42])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:28:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (26678)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.42  % (26678)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f182,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f44,f48,f53,f59,f64,f68,f72,f76,f82,f89,f157,f163,f176])).
% 0.20/0.42  fof(f176,plain,(
% 0.20/0.42    spl4_5 | ~spl4_7 | ~spl4_22),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f173])).
% 0.20/0.42  fof(f173,plain,(
% 0.20/0.42    $false | (spl4_5 | ~spl4_7 | ~spl4_22)),
% 0.20/0.42    inference(subsumption_resolution,[],[f63,f169])).
% 0.20/0.42  fof(f169,plain,(
% 0.20/0.42    ( ! [X3] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)) ) | (~spl4_7 | ~spl4_22)),
% 0.20/0.42    inference(resolution,[],[f162,f71])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f70])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    spl4_7 <=> ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.42  fof(f162,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))) ) | ~spl4_22),
% 0.20/0.42    inference(avatar_component_clause,[],[f161])).
% 0.20/0.42  fof(f161,plain,(
% 0.20/0.42    spl4_22 <=> ! [X1,X0] : ~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl4_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f61])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl4_5 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.42  fof(f163,plain,(
% 0.20/0.42    spl4_22 | ~spl4_4 | ~spl4_10 | ~spl4_21),
% 0.20/0.42    inference(avatar_split_clause,[],[f159,f155,f87,f56,f161])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl4_4 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl4_10 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.42  fof(f155,plain,(
% 0.20/0.42    spl4_21 <=> ! [X1,X0,X2] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.42  fof(f159,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))) ) | (~spl4_4 | ~spl4_10 | ~spl4_21)),
% 0.20/0.42    inference(subsumption_resolution,[],[f158,f58])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    v1_relat_1(k1_xboole_0) | ~spl4_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f56])).
% 0.20/0.42  fof(f158,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl4_10 | ~spl4_21)),
% 0.20/0.42    inference(resolution,[],[f156,f88])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f87])).
% 0.20/0.42  fof(f156,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl4_21),
% 0.20/0.42    inference(avatar_component_clause,[],[f155])).
% 0.20/0.42  fof(f157,plain,(
% 0.20/0.42    spl4_21),
% 0.20/0.42    inference(avatar_split_clause,[],[f36,f155])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(rectify,[],[f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(nnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    spl4_10 | ~spl4_7 | ~spl4_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f85,f80,f70,f87])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    spl4_9 <=> ! [X1,X0] : ~r2_hidden(X0,k4_xboole_0(X1,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl4_7 | ~spl4_9)),
% 0.20/0.42    inference(backward_demodulation,[],[f81,f83])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl4_7 | ~spl4_9)),
% 0.20/0.42    inference(resolution,[],[f81,f71])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) ) | ~spl4_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f80])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    spl4_9 | ~spl4_2 | ~spl4_6 | ~spl4_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f78,f74,f66,f46,f80])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl4_2 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    spl4_6 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    spl4_8 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) ) | (~spl4_2 | ~spl4_6 | ~spl4_8)),
% 0.20/0.42    inference(forward_demodulation,[],[f77,f67])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f66])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) ) | (~spl4_2 | ~spl4_8)),
% 0.20/0.42    inference(resolution,[],[f75,f47])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl4_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f46])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl4_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f74])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    spl4_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f39,f74])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f34,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(rectify,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    spl4_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f31,f70])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl4_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f30,f66])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    ~spl4_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f61])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.42    inference(ennf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,negated_conjecture,(
% 0.20/0.42    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.42    inference(negated_conjecture,[],[f9])).
% 0.20/0.42  fof(f9,conjecture,(
% 0.20/0.42    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    spl4_4 | ~spl4_1 | ~spl4_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f54,f50,f42,f56])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl4_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    spl4_3 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    v1_relat_1(k1_xboole_0) | (~spl4_1 | ~spl4_3)),
% 0.20/0.42    inference(superposition,[],[f43,f52])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl4_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f50])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl4_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f42])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl4_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f50])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,axiom,(
% 0.20/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    spl4_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f29,f46])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    spl4_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f42])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (26678)------------------------------
% 0.20/0.42  % (26678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (26678)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (26678)Memory used [KB]: 6140
% 0.20/0.42  % (26678)Time elapsed: 0.007 s
% 0.20/0.42  % (26678)------------------------------
% 0.20/0.42  % (26678)------------------------------
% 0.20/0.42  % (26670)Success in time 0.059 s
%------------------------------------------------------------------------------
