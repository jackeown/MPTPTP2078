%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:59 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 223 expanded)
%              Number of leaves         :   17 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  225 ( 647 expanded)
%              Number of equality atoms :   53 ( 195 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f162,f218,f225,f239,f243])).

fof(f243,plain,
    ( ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f241,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK0 != sK1
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK0 != sK1
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f241,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f187,f240])).

fof(f240,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f221,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f221,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl6_6
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f187,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f185,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f185,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_4 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f175,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f175,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK1,X1),sK0)
        | r1_tarski(sK1,X1) )
    | ~ spl6_4 ),
    inference(resolution,[],[f92,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_4
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f239,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f237,f76])).

fof(f76,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_1
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f237,plain,
    ( r2_hidden(sK2(sK1,sK0),sK1)
    | ~ spl6_4
    | spl6_6 ),
    inference(forward_demodulation,[],[f236,f200])).

fof(f200,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl6_4 ),
    inference(superposition,[],[f46,f187])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f236,plain,
    ( r2_hidden(sK2(sK1,sK0),k3_xboole_0(sK0,sK1))
    | spl6_6 ),
    inference(forward_demodulation,[],[f235,f46])).

fof(f235,plain,
    ( r2_hidden(sK2(sK1,sK0),k3_xboole_0(sK1,sK0))
    | spl6_6 ),
    inference(resolution,[],[f222,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
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
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f222,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f220])).

fof(f225,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f104,f78,f75])).

fof(f78,plain,
    ( spl6_2
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f104,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK0)
      | ~ r2_hidden(X7,sK1)
      | r2_hidden(X6,sK1) ) ),
    inference(resolution,[],[f72,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f72,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(superposition,[],[f66,f41])).

fof(f41,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f218,plain,
    ( ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f216,f44])).

fof(f44,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f216,plain,
    ( sK0 = sK1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f200,f105])).

fof(f105,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f85,f50])).

fof(f85,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f81,f52])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0,sK1),sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f79,f53])).

fof(f79,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f162,plain,
    ( spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f103,f88,f91])).

fof(f88,plain,
    ( spl6_3
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f103,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK0)
      | ~ r2_hidden(X5,sK1)
      | r2_hidden(X5,sK0) ) ),
    inference(resolution,[],[f72,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f160,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f144,f42])).

fof(f42,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f144,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_3 ),
    inference(superposition,[],[f106,f134])).

fof(f134,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f128,f54])).

fof(f128,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl6_3 ),
    inference(superposition,[],[f110,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f110,plain,
    ( ! [X2] : r1_xboole_0(sK0,k5_xboole_0(sK0,X2))
    | ~ spl6_3 ),
    inference(superposition,[],[f47,f99])).

fof(f99,plain,
    ( ! [X0] : sK0 = k3_xboole_0(sK0,X0)
    | ~ spl6_3 ),
    inference(resolution,[],[f94,f50])).

fof(f94,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | ~ spl6_3 ),
    inference(resolution,[],[f89,f52])).

fof(f89,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f106,plain,
    ( ! [X1] : sK0 = k3_xboole_0(X1,sK0)
    | ~ spl6_3 ),
    inference(superposition,[],[f99,f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (15774)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (15768)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (15770)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (15790)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (15788)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (15776)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (15776)Refutation not found, incomplete strategy% (15776)------------------------------
% 0.21/0.51  % (15776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15776)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15776)Memory used [KB]: 10618
% 0.21/0.51  % (15776)Time elapsed: 0.114 s
% 0.21/0.51  % (15776)------------------------------
% 0.21/0.51  % (15776)------------------------------
% 0.21/0.51  % (15778)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (15784)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (15782)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (15778)Refutation not found, incomplete strategy% (15778)------------------------------
% 0.21/0.52  % (15778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15778)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15778)Memory used [KB]: 10618
% 0.21/0.52  % (15778)Time elapsed: 0.118 s
% 0.21/0.52  % (15778)------------------------------
% 0.21/0.52  % (15778)------------------------------
% 0.21/0.52  % (15789)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (15771)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (15772)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (15781)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (15771)Refutation not found, incomplete strategy% (15771)------------------------------
% 0.21/0.53  % (15771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15771)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15771)Memory used [KB]: 6140
% 0.21/0.53  % (15771)Time elapsed: 0.126 s
% 0.21/0.53  % (15771)------------------------------
% 0.21/0.53  % (15771)------------------------------
% 0.21/0.53  % (15769)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.53  % (15792)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.53  % (15775)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.53  % (15785)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.53  % (15773)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.53  % (15794)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.54  % (15795)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.54  % (15783)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.54  % (15779)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.54  % (15787)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.54  % (15786)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.54  % (15793)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.54  % (15775)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.54  % (15767)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.54  % (15777)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.54  % (15767)Refutation not found, incomplete strategy% (15767)------------------------------
% 1.37/0.54  % (15767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (15767)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (15767)Memory used [KB]: 1663
% 1.37/0.54  % (15767)Time elapsed: 0.132 s
% 1.37/0.54  % (15767)------------------------------
% 1.37/0.54  % (15767)------------------------------
% 1.37/0.54  % (15787)Refutation not found, incomplete strategy% (15787)------------------------------
% 1.37/0.54  % (15787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (15780)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.54  % (15777)Refutation not found, incomplete strategy% (15777)------------------------------
% 1.37/0.54  % (15777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.55  % SZS output start Proof for theBenchmark
% 1.56/0.55  fof(f244,plain,(
% 1.56/0.55    $false),
% 1.56/0.55    inference(avatar_sat_refutation,[],[f160,f162,f218,f225,f239,f243])).
% 1.56/0.55  fof(f243,plain,(
% 1.56/0.55    ~spl6_4 | ~spl6_6),
% 1.56/0.55    inference(avatar_contradiction_clause,[],[f242])).
% 1.56/0.55  fof(f242,plain,(
% 1.56/0.55    $false | (~spl6_4 | ~spl6_6)),
% 1.56/0.55    inference(subsumption_resolution,[],[f241,f43])).
% 1.56/0.55  fof(f43,plain,(
% 1.56/0.55    k1_xboole_0 != sK1),
% 1.56/0.55    inference(cnf_transformation,[],[f26])).
% 1.56/0.55  fof(f26,plain,(
% 1.56/0.55    sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.56/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f25])).
% 1.56/0.55  fof(f25,plain,(
% 1.56/0.55    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0))),
% 1.56/0.55    introduced(choice_axiom,[])).
% 1.56/0.55  fof(f18,plain,(
% 1.56/0.55    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.56/0.55    inference(flattening,[],[f17])).
% 1.56/0.55  fof(f17,plain,(
% 1.56/0.55    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.56/0.55    inference(ennf_transformation,[],[f13])).
% 1.56/0.55  fof(f13,negated_conjecture,(
% 1.56/0.55    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.56/0.55    inference(negated_conjecture,[],[f12])).
% 1.56/0.55  fof(f12,conjecture,(
% 1.56/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 1.56/0.55  fof(f241,plain,(
% 1.56/0.55    k1_xboole_0 = sK1 | (~spl6_4 | ~spl6_6)),
% 1.56/0.55    inference(backward_demodulation,[],[f187,f240])).
% 1.56/0.55  fof(f240,plain,(
% 1.56/0.55    k1_xboole_0 = k3_xboole_0(sK1,sK0) | ~spl6_6),
% 1.56/0.55    inference(resolution,[],[f221,f54])).
% 1.56/0.55  fof(f54,plain,(
% 1.56/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.56/0.55    inference(cnf_transformation,[],[f31])).
% 1.56/0.55  fof(f31,plain,(
% 1.56/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.56/0.55    inference(nnf_transformation,[],[f4])).
% 1.56/0.55  fof(f4,axiom,(
% 1.56/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.56/0.55  fof(f221,plain,(
% 1.56/0.55    r1_xboole_0(sK1,sK0) | ~spl6_6),
% 1.56/0.55    inference(avatar_component_clause,[],[f220])).
% 1.56/0.55  fof(f220,plain,(
% 1.56/0.55    spl6_6 <=> r1_xboole_0(sK1,sK0)),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.56/0.55  fof(f187,plain,(
% 1.56/0.55    sK1 = k3_xboole_0(sK1,sK0) | ~spl6_4),
% 1.56/0.55    inference(resolution,[],[f185,f50])).
% 1.56/0.55  fof(f50,plain,(
% 1.56/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.56/0.55    inference(cnf_transformation,[],[f20])).
% 1.56/0.55  fof(f20,plain,(
% 1.56/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.56/0.55    inference(ennf_transformation,[],[f9])).
% 1.56/0.55  fof(f9,axiom,(
% 1.56/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.56/0.55  fof(f185,plain,(
% 1.56/0.55    r1_tarski(sK1,sK0) | ~spl6_4),
% 1.56/0.55    inference(duplicate_literal_removal,[],[f184])).
% 1.56/0.55  fof(f184,plain,(
% 1.56/0.55    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl6_4),
% 1.56/0.55    inference(resolution,[],[f175,f53])).
% 1.56/0.55  fof(f53,plain,(
% 1.56/0.55    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f30])).
% 1.56/0.55  fof(f30,plain,(
% 1.56/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.56/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f29])).
% 1.56/0.55  fof(f29,plain,(
% 1.56/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.56/0.55    introduced(choice_axiom,[])).
% 1.56/0.55  fof(f23,plain,(
% 1.56/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.56/0.55    inference(ennf_transformation,[],[f16])).
% 1.56/0.55  fof(f16,plain,(
% 1.56/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.56/0.55    inference(unused_predicate_definition_removal,[],[f2])).
% 1.56/0.55  fof(f2,axiom,(
% 1.56/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.55  fof(f175,plain,(
% 1.56/0.55    ( ! [X1] : (r2_hidden(sK3(sK1,X1),sK0) | r1_tarski(sK1,X1)) ) | ~spl6_4),
% 1.56/0.55    inference(resolution,[],[f92,f52])).
% 1.56/0.55  fof(f52,plain,(
% 1.56/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f30])).
% 1.56/0.55  fof(f92,plain,(
% 1.56/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | ~spl6_4),
% 1.56/0.55    inference(avatar_component_clause,[],[f91])).
% 1.56/0.55  fof(f91,plain,(
% 1.56/0.55    spl6_4 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.56/0.55  fof(f239,plain,(
% 1.56/0.55    ~spl6_1 | ~spl6_4 | spl6_6),
% 1.56/0.55    inference(avatar_contradiction_clause,[],[f238])).
% 1.56/0.55  fof(f238,plain,(
% 1.56/0.55    $false | (~spl6_1 | ~spl6_4 | spl6_6)),
% 1.56/0.55    inference(subsumption_resolution,[],[f237,f76])).
% 1.56/0.55  fof(f76,plain,(
% 1.56/0.55    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl6_1),
% 1.56/0.55    inference(avatar_component_clause,[],[f75])).
% 1.56/0.55  fof(f75,plain,(
% 1.56/0.55    spl6_1 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.56/0.55  fof(f237,plain,(
% 1.56/0.55    r2_hidden(sK2(sK1,sK0),sK1) | (~spl6_4 | spl6_6)),
% 1.56/0.55    inference(forward_demodulation,[],[f236,f200])).
% 1.56/0.55  fof(f200,plain,(
% 1.56/0.55    sK1 = k3_xboole_0(sK0,sK1) | ~spl6_4),
% 1.56/0.55    inference(superposition,[],[f46,f187])).
% 1.56/0.55  fof(f46,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f1])).
% 1.56/0.55  fof(f1,axiom,(
% 1.56/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.56/0.55  fof(f236,plain,(
% 1.56/0.55    r2_hidden(sK2(sK1,sK0),k3_xboole_0(sK0,sK1)) | spl6_6),
% 1.56/0.55    inference(forward_demodulation,[],[f235,f46])).
% 1.56/0.55  fof(f235,plain,(
% 1.56/0.55    r2_hidden(sK2(sK1,sK0),k3_xboole_0(sK1,sK0)) | spl6_6),
% 1.56/0.55    inference(resolution,[],[f222,f48])).
% 1.56/0.55  fof(f48,plain,(
% 1.56/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.56/0.55    inference(cnf_transformation,[],[f28])).
% 1.56/0.55  fof(f28,plain,(
% 1.56/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.56/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f27])).
% 1.56/0.55  fof(f27,plain,(
% 1.56/0.55    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.56/0.55    introduced(choice_axiom,[])).
% 1.56/0.55  fof(f19,plain,(
% 1.56/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.56/0.55    inference(ennf_transformation,[],[f14])).
% 1.56/0.55  fof(f14,plain,(
% 1.56/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.56/0.55    inference(rectify,[],[f6])).
% 1.56/0.55  fof(f6,axiom,(
% 1.56/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.56/0.55  fof(f222,plain,(
% 1.56/0.55    ~r1_xboole_0(sK1,sK0) | spl6_6),
% 1.56/0.55    inference(avatar_component_clause,[],[f220])).
% 1.56/0.55  fof(f225,plain,(
% 1.56/0.55    spl6_1 | spl6_2),
% 1.56/0.55    inference(avatar_split_clause,[],[f104,f78,f75])).
% 1.56/0.55  fof(f78,plain,(
% 1.56/0.55    spl6_2 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.56/0.55  fof(f104,plain,(
% 1.56/0.55    ( ! [X6,X7] : (~r2_hidden(X6,sK0) | ~r2_hidden(X7,sK1) | r2_hidden(X6,sK1)) )),
% 1.56/0.55    inference(resolution,[],[f72,f65])).
% 1.56/0.55  fof(f65,plain,(
% 1.56/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f40])).
% 1.56/0.55  fof(f40,plain,(
% 1.56/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.56/0.55    inference(flattening,[],[f39])).
% 1.56/0.55  fof(f39,plain,(
% 1.56/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.56/0.55    inference(nnf_transformation,[],[f11])).
% 1.56/0.55  fof(f11,axiom,(
% 1.56/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.56/0.55  fof(f72,plain,(
% 1.56/0.55    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK1)) )),
% 1.56/0.55    inference(superposition,[],[f66,f41])).
% 1.56/0.55  fof(f41,plain,(
% 1.56/0.55    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.56/0.55    inference(cnf_transformation,[],[f26])).
% 1.56/0.55  fof(f66,plain,(
% 1.56/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f40])).
% 1.56/0.55  fof(f218,plain,(
% 1.56/0.55    ~spl6_2 | ~spl6_4),
% 1.56/0.55    inference(avatar_contradiction_clause,[],[f217])).
% 1.56/0.55  fof(f217,plain,(
% 1.56/0.55    $false | (~spl6_2 | ~spl6_4)),
% 1.56/0.55    inference(subsumption_resolution,[],[f216,f44])).
% 1.56/0.55  fof(f44,plain,(
% 1.56/0.55    sK0 != sK1),
% 1.56/0.55    inference(cnf_transformation,[],[f26])).
% 1.56/0.55  fof(f216,plain,(
% 1.56/0.55    sK0 = sK1 | (~spl6_2 | ~spl6_4)),
% 1.56/0.55    inference(forward_demodulation,[],[f200,f105])).
% 1.56/0.55  fof(f105,plain,(
% 1.56/0.55    sK0 = k3_xboole_0(sK0,sK1) | ~spl6_2),
% 1.56/0.55    inference(resolution,[],[f85,f50])).
% 1.56/0.55  fof(f85,plain,(
% 1.56/0.55    r1_tarski(sK0,sK1) | ~spl6_2),
% 1.56/0.55    inference(duplicate_literal_removal,[],[f84])).
% 1.56/0.55  fof(f84,plain,(
% 1.56/0.55    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl6_2),
% 1.56/0.55    inference(resolution,[],[f81,f52])).
% 1.56/0.55  fof(f81,plain,(
% 1.56/0.55    ( ! [X0] : (~r2_hidden(sK3(X0,sK1),sK0) | r1_tarski(X0,sK1)) ) | ~spl6_2),
% 1.56/0.55    inference(resolution,[],[f79,f53])).
% 1.56/0.55  fof(f79,plain,(
% 1.56/0.55    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl6_2),
% 1.56/0.55    inference(avatar_component_clause,[],[f78])).
% 1.56/0.55  fof(f162,plain,(
% 1.56/0.55    spl6_4 | spl6_3),
% 1.56/0.55    inference(avatar_split_clause,[],[f103,f88,f91])).
% 1.56/0.55  fof(f88,plain,(
% 1.56/0.55    spl6_3 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.56/0.55  fof(f103,plain,(
% 1.56/0.55    ( ! [X4,X5] : (~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK1) | r2_hidden(X5,sK0)) )),
% 1.56/0.55    inference(resolution,[],[f72,f64])).
% 1.56/0.55  fof(f64,plain,(
% 1.56/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f40])).
% 1.56/0.55  fof(f160,plain,(
% 1.56/0.55    ~spl6_3),
% 1.56/0.55    inference(avatar_contradiction_clause,[],[f159])).
% 1.56/0.55  fof(f159,plain,(
% 1.56/0.55    $false | ~spl6_3),
% 1.56/0.55    inference(subsumption_resolution,[],[f144,f42])).
% 1.56/0.55  fof(f42,plain,(
% 1.56/0.55    k1_xboole_0 != sK0),
% 1.56/0.55    inference(cnf_transformation,[],[f26])).
% 1.56/0.55  fof(f144,plain,(
% 1.56/0.55    k1_xboole_0 = sK0 | ~spl6_3),
% 1.56/0.55    inference(superposition,[],[f106,f134])).
% 1.56/0.55  fof(f134,plain,(
% 1.56/0.55    k1_xboole_0 = k3_xboole_0(sK0,sK0) | ~spl6_3),
% 1.56/0.55    inference(resolution,[],[f128,f54])).
% 1.56/0.55  fof(f128,plain,(
% 1.56/0.55    r1_xboole_0(sK0,sK0) | ~spl6_3),
% 1.56/0.55    inference(superposition,[],[f110,f45])).
% 1.56/0.55  fof(f45,plain,(
% 1.56/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.56/0.55    inference(cnf_transformation,[],[f10])).
% 1.56/0.55  fof(f10,axiom,(
% 1.56/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.56/0.55  fof(f110,plain,(
% 1.56/0.55    ( ! [X2] : (r1_xboole_0(sK0,k5_xboole_0(sK0,X2))) ) | ~spl6_3),
% 1.56/0.55    inference(superposition,[],[f47,f99])).
% 1.56/0.55  fof(f99,plain,(
% 1.56/0.55    ( ! [X0] : (sK0 = k3_xboole_0(sK0,X0)) ) | ~spl6_3),
% 1.56/0.55    inference(resolution,[],[f94,f50])).
% 1.56/0.55  fof(f94,plain,(
% 1.56/0.55    ( ! [X0] : (r1_tarski(sK0,X0)) ) | ~spl6_3),
% 1.56/0.55    inference(resolution,[],[f89,f52])).
% 1.56/0.55  fof(f89,plain,(
% 1.56/0.55    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl6_3),
% 1.56/0.55    inference(avatar_component_clause,[],[f88])).
% 1.56/0.55  fof(f47,plain,(
% 1.56/0.55    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.56/0.55    inference(cnf_transformation,[],[f8])).
% 1.56/0.55  fof(f8,axiom,(
% 1.56/0.55    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.56/0.55  fof(f106,plain,(
% 1.56/0.55    ( ! [X1] : (sK0 = k3_xboole_0(X1,sK0)) ) | ~spl6_3),
% 1.56/0.55    inference(superposition,[],[f99,f46])).
% 1.56/0.55  % SZS output end Proof for theBenchmark
% 1.56/0.55  % (15775)------------------------------
% 1.56/0.55  % (15775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.55  % (15775)Termination reason: Refutation
% 1.56/0.55  
% 1.56/0.55  % (15775)Memory used [KB]: 10746
% 1.56/0.55  % (15775)Time elapsed: 0.136 s
% 1.56/0.55  % (15775)------------------------------
% 1.56/0.55  % (15775)------------------------------
% 1.56/0.55  % (15791)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.56/0.55  % (15766)Success in time 0.195 s
%------------------------------------------------------------------------------
