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
% DateTime   : Thu Dec  3 13:00:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 815 expanded)
%              Number of leaves         :   28 ( 255 expanded)
%              Depth                    :   29
%              Number of atoms          :  709 (2921 expanded)
%              Number of equality atoms :   97 ( 615 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f775,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f297,f491,f494,f519,f717,f720,f748,f753,f774])).

fof(f774,plain,
    ( spl8_3
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f773])).

fof(f773,plain,
    ( $false
    | spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f772,f59])).

fof(f59,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( sK4 != sK5
    & r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))
    & v3_ordinal1(sK5)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f17,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK4 != X1
          & r4_wellord1(k1_wellord2(sK4),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( sK4 != X1
        & r4_wellord1(k1_wellord2(sK4),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK4 != sK5
      & r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f772,plain,
    ( ~ v3_ordinal1(sK4)
    | spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f771,f471])).

fof(f471,plain,
    ( sK4 != k1_wellord1(k1_wellord2(sK4),sK4)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl8_3
  <=> sK4 = k1_wellord1(k1_wellord2(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f771,plain,
    ( sK4 = k1_wellord1(k1_wellord2(sK4),sK4)
    | ~ v3_ordinal1(sK4)
    | ~ spl8_6 ),
    inference(duplicate_literal_removal,[],[f770])).

fof(f770,plain,
    ( sK4 = k1_wellord1(k1_wellord2(sK4),sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK4)
    | ~ spl8_6 ),
    inference(resolution,[],[f489,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f489,plain,
    ( r2_hidden(sK4,sK4)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f488])).

fof(f488,plain,
    ( spl8_6
  <=> r2_hidden(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f753,plain,
    ( spl8_8
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f752])).

fof(f752,plain,
    ( $false
    | spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f751,f59])).

fof(f751,plain,
    ( ~ v3_ordinal1(sK4)
    | spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f750,f60])).

fof(f60,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f750,plain,
    ( ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4)
    | spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f749,f701])).

fof(f701,plain,
    ( sK4 != k1_wellord1(k1_wellord2(sK5),sK4)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f700])).

fof(f700,plain,
    ( spl8_8
  <=> sK4 = k1_wellord1(k1_wellord2(sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f749,plain,
    ( sK4 = k1_wellord1(k1_wellord2(sK5),sK4)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4)
    | ~ spl8_10 ),
    inference(resolution,[],[f715,f68])).

fof(f715,plain,
    ( r2_hidden(sK4,sK5)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f714])).

fof(f714,plain,
    ( spl8_10
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f748,plain,
    ( ~ spl8_1
    | ~ spl8_9
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f747])).

fof(f747,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f746,f60])).

fof(f746,plain,
    ( ~ v3_ordinal1(sK5)
    | ~ spl8_1
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f745,f62])).

fof(f62,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f45])).

fof(f745,plain,
    ( sK4 = sK5
    | ~ v3_ordinal1(sK5)
    | ~ spl8_1
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f740,f716])).

fof(f716,plain,
    ( ~ r2_hidden(sK4,sK5)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f714])).

fof(f740,plain,
    ( r2_hidden(sK4,sK5)
    | sK4 = sK5
    | ~ v3_ordinal1(sK5)
    | ~ spl8_1
    | ~ spl8_9
    | spl8_10 ),
    inference(resolution,[],[f738,f593])).

fof(f593,plain,
    ( ! [X7] :
        ( r2_hidden(sK4,X7)
        | r2_hidden(X7,sK5)
        | sK4 = X7
        | ~ v3_ordinal1(X7) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f586,f59])).

fof(f586,plain,
    ( ! [X7] :
        ( r2_hidden(X7,sK5)
        | r2_hidden(sK4,X7)
        | sK4 = X7
        | ~ v3_ordinal1(sK4)
        | ~ v3_ordinal1(X7) )
    | ~ spl8_1 ),
    inference(resolution,[],[f548,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f548,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK4)
        | r2_hidden(X2,sK5) )
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f547,f99])).

fof(f99,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f98,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | k3_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ sP1(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP1(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ sP1(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP1(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( sP1(X1,X0)
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f98,plain,(
    ! [X0] : sP2(X0,k1_wellord2(X0)) ),
    inference(subsumption_resolution,[],[f97,f63])).

fof(f63,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f97,plain,(
    ! [X0] :
      ( sP2(X0,k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f93,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f30,f41,f40,f39,f38])).

fof(f38,plain,(
    ! [X3,X2,X1] :
      ( sP0(X3,X2,X1)
    <=> ( r2_hidden(k4_tarski(X2,X3),X1)
      <=> r1_tarski(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f39,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ! [X2,X3] :
          ( sP0(X3,X2,X1)
          | ~ r2_hidden(X3,X0)
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ( k1_wellord2(X0) = X1
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

% (23909)Refutation not found, incomplete strategy% (23909)------------------------------
% (23909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23909)Termination reason: Refutation not found, incomplete strategy

% (23909)Memory used [KB]: 1663
% (23909)Time elapsed: 0.118 s
% (23909)------------------------------
% (23909)------------------------------
fof(f93,plain,(
    ! [X1] :
      ( ~ sP3(k1_wellord2(X1),X1)
      | sP2(X1,k1_wellord2(X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k1_wellord2(X1) != X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X1) = X0
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | k1_wellord2(X1) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f547,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK4)
        | r2_hidden(X2,k3_relat_1(k1_wellord2(sK5))) )
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f546,f99])).

fof(f546,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_relat_1(k1_wellord2(sK4)))
        | r2_hidden(X2,k3_relat_1(k1_wellord2(sK5))) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f529,f63])).

fof(f529,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_relat_1(k1_wellord2(sK4)))
        | r2_hidden(X2,k3_relat_1(k1_wellord2(sK5)))
        | ~ v1_relat_1(k1_wellord2(sK5)) )
    | ~ spl8_1 ),
    inference(superposition,[],[f91,f292])).

fof(f292,plain,
    ( k1_wellord2(sK4) = k2_wellord1(k1_wellord2(sK5),sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl8_1
  <=> k1_wellord2(sK4) = k2_wellord1(k1_wellord2(sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

% (23911)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(f738,plain,
    ( ~ r2_hidden(sK5,sK5)
    | ~ spl8_1
    | ~ spl8_9
    | spl8_10 ),
    inference(forward_demodulation,[],[f737,f99])).

fof(f737,plain,
    ( ~ r2_hidden(sK5,k3_relat_1(k1_wellord2(sK5)))
    | ~ spl8_1
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f736,f185])).

fof(f185,plain,(
    r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK5)) ),
    inference(subsumption_resolution,[],[f184,f63])).

fof(f184,plain,
    ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK5))
    | ~ v1_relat_1(k1_wellord2(sK5)) ),
    inference(resolution,[],[f181,f105])).

fof(f105,plain,(
    r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) ),
    inference(subsumption_resolution,[],[f104,f63])).

fof(f104,plain,
    ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4))
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(subsumption_resolution,[],[f103,f63])).

fof(f103,plain,
    ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4))
    | ~ v1_relat_1(k1_wellord2(sK5))
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(resolution,[],[f65,f61])).

fof(f61,plain,(
    r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f181,plain,(
    ! [X0] :
      ( ~ r4_wellord1(X0,k1_wellord2(sK4))
      | r4_wellord1(X0,k1_wellord2(sK5))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f180,f63])).

fof(f180,plain,(
    ! [X0] :
      ( r4_wellord1(X0,k1_wellord2(sK5))
      | ~ r4_wellord1(X0,k1_wellord2(sK4))
      | ~ v1_relat_1(k1_wellord2(sK4))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f178,f63])).

fof(f178,plain,(
    ! [X0] :
      ( r4_wellord1(X0,k1_wellord2(sK5))
      | ~ r4_wellord1(X0,k1_wellord2(sK4))
      | ~ v1_relat_1(k1_wellord2(sK5))
      | ~ v1_relat_1(k1_wellord2(sK4))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f66,f61])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_wellord1(X1,X2)
      | r4_wellord1(X0,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).

fof(f736,plain,
    ( ~ r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK5))
    | ~ r2_hidden(sK5,k3_relat_1(k1_wellord2(sK5)))
    | ~ spl8_1
    | ~ spl8_9
    | spl8_10 ),
    inference(forward_demodulation,[],[f735,f109])).

fof(f109,plain,(
    ! [X0] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0) ),
    inference(resolution,[],[f84,f95])).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f735,plain,
    ( ~ r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK5))
    | ~ r2_hidden(sK5,k3_relat_1(k1_wellord2(sK5)))
    | ~ spl8_1
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f734,f63])).

fof(f734,plain,
    ( ~ r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK5))
    | ~ r2_hidden(sK5,k3_relat_1(k1_wellord2(sK5)))
    | ~ v1_relat_1(k1_wellord2(sK5))
    | ~ spl8_1
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f733,f711])).

fof(f711,plain,
    ( v2_wellord1(k1_wellord2(sK5))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f710])).

fof(f710,plain,
    ( spl8_9
  <=> v2_wellord1(k1_wellord2(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f733,plain,
    ( ~ r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK5))
    | ~ r2_hidden(sK5,k3_relat_1(k1_wellord2(sK5)))
    | ~ v2_wellord1(k1_wellord2(sK5))
    | ~ v1_relat_1(k1_wellord2(sK5))
    | ~ spl8_1
    | spl8_10 ),
    inference(superposition,[],[f64,f729])).

fof(f729,plain,
    ( sK5 = k1_wellord1(k1_wellord2(sK5),sK5)
    | ~ spl8_1
    | spl8_10 ),
    inference(subsumption_resolution,[],[f728,f60])).

fof(f728,plain,
    ( ~ v3_ordinal1(sK5)
    | sK5 = k1_wellord1(k1_wellord2(sK5),sK5)
    | ~ spl8_1
    | spl8_10 ),
    inference(subsumption_resolution,[],[f723,f62])).

fof(f723,plain,
    ( sK4 = sK5
    | ~ v3_ordinal1(sK5)
    | sK5 = k1_wellord1(k1_wellord2(sK5),sK5)
    | ~ spl8_1
    | spl8_10 ),
    inference(resolution,[],[f716,f612])).

fof(f612,plain,
    ( ! [X0] :
        ( r2_hidden(sK4,X0)
        | sK4 = X0
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK5),X0) = X0 )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f610,f60])).

fof(f610,plain,
    ( ! [X0] :
        ( r2_hidden(sK4,X0)
        | sK4 = X0
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK5),X0) = X0
        | ~ v3_ordinal1(sK5) )
    | ~ spl8_1 ),
    inference(duplicate_literal_removal,[],[f606])).

fof(f606,plain,
    ( ! [X0] :
        ( r2_hidden(sK4,X0)
        | sK4 = X0
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK5),X0) = X0
        | ~ v3_ordinal1(sK5)
        | ~ v3_ordinal1(X0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f593,f68])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f720,plain,(
    spl8_9 ),
    inference(avatar_contradiction_clause,[],[f719])).

fof(f719,plain,
    ( $false
    | spl8_9 ),
    inference(subsumption_resolution,[],[f718,f60])).

fof(f718,plain,
    ( ~ v3_ordinal1(sK5)
    | spl8_9 ),
    inference(resolution,[],[f712,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f712,plain,
    ( ~ v2_wellord1(k1_wellord2(sK5))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f710])).

fof(f717,plain,
    ( ~ spl8_9
    | ~ spl8_10
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f708,f700,f290,f714,f710])).

fof(f708,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ v2_wellord1(k1_wellord2(sK5))
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f707,f99])).

% (23903)Refutation not found, incomplete strategy% (23903)------------------------------
% (23903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23903)Termination reason: Refutation not found, incomplete strategy

% (23903)Memory used [KB]: 10618
% (23903)Time elapsed: 0.119 s
% (23903)------------------------------
% (23903)------------------------------
fof(f707,plain,
    ( ~ r2_hidden(sK4,k3_relat_1(k1_wellord2(sK5)))
    | ~ v2_wellord1(k1_wellord2(sK5))
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f706,f105])).

fof(f706,plain,
    ( ~ r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4))
    | ~ r2_hidden(sK4,k3_relat_1(k1_wellord2(sK5)))
    | ~ v2_wellord1(k1_wellord2(sK5))
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f705,f292])).

fof(f705,plain,
    ( ~ r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK4))
    | ~ r2_hidden(sK4,k3_relat_1(k1_wellord2(sK5)))
    | ~ v2_wellord1(k1_wellord2(sK5))
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f704,f63])).

fof(f704,plain,
    ( ~ r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK4))
    | ~ r2_hidden(sK4,k3_relat_1(k1_wellord2(sK5)))
    | ~ v2_wellord1(k1_wellord2(sK5))
    | ~ v1_relat_1(k1_wellord2(sK5))
    | ~ spl8_8 ),
    inference(superposition,[],[f64,f702])).

fof(f702,plain,
    ( sK4 = k1_wellord1(k1_wellord2(sK5),sK4)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f700])).

fof(f519,plain,
    ( ~ spl8_2
    | ~ spl8_5
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f517,f59])).

fof(f517,plain,
    ( ~ v3_ordinal1(sK4)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f516,f62])).

fof(f516,plain,
    ( sK4 = sK5
    | ~ v3_ordinal1(sK4)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f512,f490])).

fof(f490,plain,
    ( ~ r2_hidden(sK4,sK4)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f488])).

fof(f512,plain,
    ( r2_hidden(sK4,sK4)
    | sK4 = sK5
    | ~ v3_ordinal1(sK4)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_6 ),
    inference(resolution,[],[f508,f365])).

fof(f365,plain,
    ( ! [X7] :
        ( r2_hidden(sK5,X7)
        | r2_hidden(X7,sK4)
        | sK5 = X7
        | ~ v3_ordinal1(X7) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f358,f60])).

fof(f358,plain,
    ( ! [X7] :
        ( r2_hidden(X7,sK4)
        | r2_hidden(sK5,X7)
        | sK5 = X7
        | ~ v3_ordinal1(sK5)
        | ~ v3_ordinal1(X7) )
    | ~ spl8_2 ),
    inference(resolution,[],[f320,f69])).

fof(f320,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK5)
        | r2_hidden(X2,sK4) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f319,f99])).

fof(f319,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK5)
        | r2_hidden(X2,k3_relat_1(k1_wellord2(sK4))) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f318,f99])).

fof(f318,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_relat_1(k1_wellord2(sK5)))
        | r2_hidden(X2,k3_relat_1(k1_wellord2(sK4))) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f301,f63])).

fof(f301,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_relat_1(k1_wellord2(sK5)))
        | r2_hidden(X2,k3_relat_1(k1_wellord2(sK4)))
        | ~ v1_relat_1(k1_wellord2(sK4)) )
    | ~ spl8_2 ),
    inference(superposition,[],[f91,f296])).

fof(f296,plain,
    ( k1_wellord2(sK5) = k2_wellord1(k1_wellord2(sK4),sK5)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl8_2
  <=> k1_wellord2(sK5) = k2_wellord1(k1_wellord2(sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f508,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_6 ),
    inference(forward_demodulation,[],[f507,f99])).

fof(f507,plain,
    ( ~ r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4)))
    | ~ spl8_2
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f506,f61])).

fof(f506,plain,
    ( ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))
    | ~ r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4)))
    | ~ spl8_2
    | ~ spl8_5
    | spl8_6 ),
    inference(forward_demodulation,[],[f505,f296])).

fof(f505,plain,
    ( ~ r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK5))
    | ~ r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4)))
    | ~ spl8_2
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f504,f63])).

fof(f504,plain,
    ( ~ r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK5))
    | ~ r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4)))
    | ~ v1_relat_1(k1_wellord2(sK4))
    | ~ spl8_2
    | ~ spl8_5
    | spl8_6 ),
    inference(subsumption_resolution,[],[f503,f485])).

fof(f485,plain,
    ( v2_wellord1(k1_wellord2(sK4))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl8_5
  <=> v2_wellord1(k1_wellord2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f503,plain,
    ( ~ r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK5))
    | ~ r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4)))
    | ~ v2_wellord1(k1_wellord2(sK4))
    | ~ v1_relat_1(k1_wellord2(sK4))
    | ~ spl8_2
    | spl8_6 ),
    inference(superposition,[],[f64,f502])).

fof(f502,plain,
    ( sK5 = k1_wellord1(k1_wellord2(sK4),sK5)
    | ~ spl8_2
    | spl8_6 ),
    inference(subsumption_resolution,[],[f501,f59])).

fof(f501,plain,
    ( ~ v3_ordinal1(sK4)
    | sK5 = k1_wellord1(k1_wellord2(sK4),sK5)
    | ~ spl8_2
    | spl8_6 ),
    inference(subsumption_resolution,[],[f495,f62])).

fof(f495,plain,
    ( sK4 = sK5
    | ~ v3_ordinal1(sK4)
    | sK5 = k1_wellord1(k1_wellord2(sK4),sK5)
    | ~ spl8_2
    | spl8_6 ),
    inference(resolution,[],[f490,f364])).

fof(f364,plain,
    ( ! [X6] :
        ( r2_hidden(X6,sK4)
        | sK5 = X6
        | ~ v3_ordinal1(X6)
        | sK5 = k1_wellord1(k1_wellord2(X6),sK5) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f357,f60])).

fof(f357,plain,
    ( ! [X6] :
        ( r2_hidden(X6,sK4)
        | sK5 = X6
        | ~ v3_ordinal1(sK5)
        | ~ v3_ordinal1(X6)
        | sK5 = k1_wellord1(k1_wellord2(X6),sK5) )
    | ~ spl8_2 ),
    inference(resolution,[],[f320,f169])).

fof(f169,plain,(
    ! [X6,X7] :
      ( r2_hidden(X7,X6)
      | X6 = X7
      | ~ v3_ordinal1(X6)
      | ~ v3_ordinal1(X7)
      | k1_wellord1(k1_wellord2(X7),X6) = X6 ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X6,X7] :
      ( r2_hidden(X7,X6)
      | X6 = X7
      | ~ v3_ordinal1(X6)
      | ~ v3_ordinal1(X7)
      | k1_wellord1(k1_wellord2(X7),X6) = X6
      | ~ v3_ordinal1(X7)
      | ~ v3_ordinal1(X6) ) ),
    inference(resolution,[],[f69,f68])).

fof(f494,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f493])).

fof(f493,plain,
    ( $false
    | spl8_5 ),
    inference(subsumption_resolution,[],[f492,f59])).

fof(f492,plain,
    ( ~ v3_ordinal1(sK4)
    | spl8_5 ),
    inference(resolution,[],[f486,f67])).

fof(f486,plain,
    ( ~ v2_wellord1(k1_wellord2(sK4))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f484])).

fof(f491,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f482,f470,f488,f484])).

fof(f482,plain,
    ( ~ r2_hidden(sK4,sK4)
    | ~ v2_wellord1(k1_wellord2(sK4))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f481,f99])).

fof(f481,plain,
    ( ~ r2_hidden(sK4,k3_relat_1(k1_wellord2(sK4)))
    | ~ v2_wellord1(k1_wellord2(sK4))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f480,f192])).

fof(f192,plain,(
    r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK4)) ),
    inference(subsumption_resolution,[],[f190,f63])).

fof(f190,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK4))
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(resolution,[],[f183,f61])).

fof(f183,plain,(
    ! [X1] :
      ( ~ r4_wellord1(X1,k1_wellord2(sK5))
      | r4_wellord1(X1,k1_wellord2(sK4))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f182,f63])).

fof(f182,plain,(
    ! [X1] :
      ( r4_wellord1(X1,k1_wellord2(sK4))
      | ~ r4_wellord1(X1,k1_wellord2(sK5))
      | ~ v1_relat_1(k1_wellord2(sK5))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f179,f63])).

fof(f179,plain,(
    ! [X1] :
      ( r4_wellord1(X1,k1_wellord2(sK4))
      | ~ r4_wellord1(X1,k1_wellord2(sK5))
      | ~ v1_relat_1(k1_wellord2(sK4))
      | ~ v1_relat_1(k1_wellord2(sK5))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f66,f105])).

fof(f480,plain,
    ( ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK4))
    | ~ r2_hidden(sK4,k3_relat_1(k1_wellord2(sK4)))
    | ~ v2_wellord1(k1_wellord2(sK4))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f479,f109])).

fof(f479,plain,
    ( ~ r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK4))
    | ~ r2_hidden(sK4,k3_relat_1(k1_wellord2(sK4)))
    | ~ v2_wellord1(k1_wellord2(sK4))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f478,f63])).

fof(f478,plain,
    ( ~ r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK4))
    | ~ r2_hidden(sK4,k3_relat_1(k1_wellord2(sK4)))
    | ~ v2_wellord1(k1_wellord2(sK4))
    | ~ v1_relat_1(k1_wellord2(sK4))
    | ~ spl8_3 ),
    inference(superposition,[],[f64,f472])).

fof(f472,plain,
    ( sK4 = k1_wellord1(k1_wellord2(sK4),sK4)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f470])).

fof(f297,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f287,f294,f290])).

fof(f287,plain,
    ( k1_wellord2(sK5) = k2_wellord1(k1_wellord2(sK4),sK5)
    | k1_wellord2(sK4) = k2_wellord1(k1_wellord2(sK5),sK4) ),
    inference(resolution,[],[f284,f60])).

fof(f284,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(sK4),X0)
      | k1_wellord2(sK4) = k2_wellord1(k1_wellord2(X0),sK4) ) ),
    inference(resolution,[],[f173,f59])).

fof(f173,plain,(
    ! [X2,X3] :
      ( ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | k1_wellord2(X2) = k2_wellord1(k1_wellord2(X3),X2)
      | k1_wellord2(X3) = k2_wellord1(k1_wellord2(X2),X3) ) ),
    inference(resolution,[],[f123,f84])).

fof(f123,plain,(
    ! [X2,X3] :
      ( r1_tarski(X3,X2)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X3)
      | k1_wellord2(X2) = k2_wellord1(k1_wellord2(X3),X2) ) ),
    inference(resolution,[],[f121,f84])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f117,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f86,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (23910)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.47  % (23906)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.48  % (23927)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (23912)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (23927)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (23903)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (23902)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (23926)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (23902)Refutation not found, incomplete strategy% (23902)------------------------------
% 0.22/0.53  % (23902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23902)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23902)Memory used [KB]: 10618
% 0.22/0.53  % (23902)Time elapsed: 0.099 s
% 0.22/0.53  % (23902)------------------------------
% 0.22/0.53  % (23902)------------------------------
% 0.22/0.53  % (23909)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f775,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f297,f491,f494,f519,f717,f720,f748,f753,f774])).
% 0.22/0.54  fof(f774,plain,(
% 0.22/0.54    spl8_3 | ~spl8_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f773])).
% 0.22/0.54  fof(f773,plain,(
% 0.22/0.54    $false | (spl8_3 | ~spl8_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f772,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    v3_ordinal1(sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    (sK4 != sK5 & r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) & v3_ordinal1(sK5)) & v3_ordinal1(sK4)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f17,f44,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK4 != X1 & r4_wellord1(k1_wellord2(sK4),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK4))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ? [X1] : (sK4 != X1 & r4_wellord1(k1_wellord2(sK4),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK4 != sK5 & r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) & v3_ordinal1(sK5))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f14])).
% 0.22/0.54  fof(f14,conjecture,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.22/0.54  fof(f772,plain,(
% 0.22/0.54    ~v3_ordinal1(sK4) | (spl8_3 | ~spl8_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f771,f471])).
% 0.22/0.54  fof(f471,plain,(
% 0.22/0.54    sK4 != k1_wellord1(k1_wellord2(sK4),sK4) | spl8_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f470])).
% 0.22/0.54  fof(f470,plain,(
% 0.22/0.54    spl8_3 <=> sK4 = k1_wellord1(k1_wellord2(sK4),sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.54  fof(f771,plain,(
% 0.22/0.54    sK4 = k1_wellord1(k1_wellord2(sK4),sK4) | ~v3_ordinal1(sK4) | ~spl8_6),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f770])).
% 0.22/0.54  fof(f770,plain,(
% 0.22/0.54    sK4 = k1_wellord1(k1_wellord2(sK4),sK4) | ~v3_ordinal1(sK4) | ~v3_ordinal1(sK4) | ~spl8_6),
% 0.22/0.54    inference(resolution,[],[f489,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.22/0.54  fof(f489,plain,(
% 0.22/0.54    r2_hidden(sK4,sK4) | ~spl8_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f488])).
% 0.22/0.54  fof(f488,plain,(
% 0.22/0.54    spl8_6 <=> r2_hidden(sK4,sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.54  fof(f753,plain,(
% 0.22/0.54    spl8_8 | ~spl8_10),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f752])).
% 0.22/0.54  fof(f752,plain,(
% 0.22/0.54    $false | (spl8_8 | ~spl8_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f751,f59])).
% 0.22/0.54  fof(f751,plain,(
% 0.22/0.54    ~v3_ordinal1(sK4) | (spl8_8 | ~spl8_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f750,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    v3_ordinal1(sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f750,plain,(
% 0.22/0.54    ~v3_ordinal1(sK5) | ~v3_ordinal1(sK4) | (spl8_8 | ~spl8_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f749,f701])).
% 0.22/0.54  fof(f701,plain,(
% 0.22/0.54    sK4 != k1_wellord1(k1_wellord2(sK5),sK4) | spl8_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f700])).
% 0.22/0.54  fof(f700,plain,(
% 0.22/0.54    spl8_8 <=> sK4 = k1_wellord1(k1_wellord2(sK5),sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.54  fof(f749,plain,(
% 0.22/0.54    sK4 = k1_wellord1(k1_wellord2(sK5),sK4) | ~v3_ordinal1(sK5) | ~v3_ordinal1(sK4) | ~spl8_10),
% 0.22/0.54    inference(resolution,[],[f715,f68])).
% 0.22/0.54  fof(f715,plain,(
% 0.22/0.54    r2_hidden(sK4,sK5) | ~spl8_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f714])).
% 0.22/0.54  fof(f714,plain,(
% 0.22/0.54    spl8_10 <=> r2_hidden(sK4,sK5)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.54  fof(f748,plain,(
% 0.22/0.54    ~spl8_1 | ~spl8_9 | spl8_10),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f747])).
% 0.22/0.54  fof(f747,plain,(
% 0.22/0.54    $false | (~spl8_1 | ~spl8_9 | spl8_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f746,f60])).
% 0.22/0.54  fof(f746,plain,(
% 0.22/0.54    ~v3_ordinal1(sK5) | (~spl8_1 | ~spl8_9 | spl8_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f745,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    sK4 != sK5),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f745,plain,(
% 0.22/0.54    sK4 = sK5 | ~v3_ordinal1(sK5) | (~spl8_1 | ~spl8_9 | spl8_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f740,f716])).
% 0.22/0.54  fof(f716,plain,(
% 0.22/0.54    ~r2_hidden(sK4,sK5) | spl8_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f714])).
% 0.22/0.54  fof(f740,plain,(
% 0.22/0.54    r2_hidden(sK4,sK5) | sK4 = sK5 | ~v3_ordinal1(sK5) | (~spl8_1 | ~spl8_9 | spl8_10)),
% 0.22/0.54    inference(resolution,[],[f738,f593])).
% 0.22/0.54  fof(f593,plain,(
% 0.22/0.54    ( ! [X7] : (r2_hidden(sK4,X7) | r2_hidden(X7,sK5) | sK4 = X7 | ~v3_ordinal1(X7)) ) | ~spl8_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f586,f59])).
% 0.22/0.54  fof(f586,plain,(
% 0.22/0.54    ( ! [X7] : (r2_hidden(X7,sK5) | r2_hidden(sK4,X7) | sK4 = X7 | ~v3_ordinal1(sK4) | ~v3_ordinal1(X7)) ) | ~spl8_1),
% 0.22/0.54    inference(resolution,[],[f548,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.54  fof(f548,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,sK4) | r2_hidden(X2,sK5)) ) | ~spl8_1),
% 0.22/0.54    inference(forward_demodulation,[],[f547,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.54    inference(resolution,[],[f98,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~sP2(X0,X1) | k3_relat_1(X1) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ! [X0,X1] : ((sP2(X0,X1) | ~sP1(X1,X0) | k3_relat_1(X1) != X0) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 0.22/0.54    inference(flattening,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(X1,X0) | k3_relat_1(X1) != X0)) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1] : (sP2(X0,X1) <=> (sP1(X1,X0) & k3_relat_1(X1) = X0))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X0] : (sP2(X0,k1_wellord2(X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f97,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X0] : (sP2(X0,k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.54    inference(resolution,[],[f93,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(definition_folding,[],[f30,f41,f40,f39,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X3,X2,X1] : (sP0(X3,X2,X1) <=> (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X1,X0] : (sP1(X1,X0) <=> ! [X2,X3] : (sP0(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X1,X0] : ((k1_wellord2(X0) = X1 <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.54  % (23909)Refutation not found, incomplete strategy% (23909)------------------------------
% 0.22/0.54  % (23909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23909)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23909)Memory used [KB]: 1663
% 0.22/0.54  % (23909)Time elapsed: 0.118 s
% 0.22/0.54  % (23909)------------------------------
% 0.22/0.54  % (23909)------------------------------
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X1] : (~sP3(k1_wellord2(X1),X1) | sP2(X1,k1_wellord2(X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP2(X1,X0) | k1_wellord2(X1) != X0 | ~sP3(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X0,X1] : (((k1_wellord2(X1) = X0 | ~sP2(X1,X0)) & (sP2(X1,X0) | k1_wellord2(X1) != X0)) | ~sP3(X0,X1))),
% 0.22/0.54    inference(rectify,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X1,X0] : (((k1_wellord2(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k1_wellord2(X0) != X1)) | ~sP3(X1,X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f41])).
% 0.22/0.54  fof(f547,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,sK4) | r2_hidden(X2,k3_relat_1(k1_wellord2(sK5)))) ) | ~spl8_1),
% 0.22/0.54    inference(forward_demodulation,[],[f546,f99])).
% 0.22/0.54  fof(f546,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,k3_relat_1(k1_wellord2(sK4))) | r2_hidden(X2,k3_relat_1(k1_wellord2(sK5)))) ) | ~spl8_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f529,f63])).
% 0.22/0.54  fof(f529,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,k3_relat_1(k1_wellord2(sK4))) | r2_hidden(X2,k3_relat_1(k1_wellord2(sK5))) | ~v1_relat_1(k1_wellord2(sK5))) ) | ~spl8_1),
% 0.22/0.54    inference(superposition,[],[f91,f292])).
% 0.22/0.54  fof(f292,plain,(
% 0.22/0.54    k1_wellord2(sK4) = k2_wellord1(k1_wellord2(sK5),sK4) | ~spl8_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f290])).
% 0.22/0.54  fof(f290,plain,(
% 0.22/0.54    spl8_1 <=> k1_wellord2(sK4) = k2_wellord1(k1_wellord2(sK5),sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.54  % (23911)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | r2_hidden(X0,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).
% 0.22/0.54  fof(f738,plain,(
% 0.22/0.54    ~r2_hidden(sK5,sK5) | (~spl8_1 | ~spl8_9 | spl8_10)),
% 0.22/0.54    inference(forward_demodulation,[],[f737,f99])).
% 0.22/0.54  fof(f737,plain,(
% 0.22/0.54    ~r2_hidden(sK5,k3_relat_1(k1_wellord2(sK5))) | (~spl8_1 | ~spl8_9 | spl8_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f736,f185])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK5))),
% 0.22/0.54    inference(subsumption_resolution,[],[f184,f63])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK5)) | ~v1_relat_1(k1_wellord2(sK5))),
% 0.22/0.54    inference(resolution,[],[f181,f105])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4))),
% 0.22/0.54    inference(subsumption_resolution,[],[f104,f63])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) | ~v1_relat_1(k1_wellord2(sK4))),
% 0.22/0.54    inference(subsumption_resolution,[],[f103,f63])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) | ~v1_relat_1(k1_wellord2(sK5)) | ~v1_relat_1(k1_wellord2(sK4))),
% 0.22/0.54    inference(resolution,[],[f65,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r4_wellord1(X0,X1) | r4_wellord1(X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    ( ! [X0] : (~r4_wellord1(X0,k1_wellord2(sK4)) | r4_wellord1(X0,k1_wellord2(sK5)) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f180,f63])).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    ( ! [X0] : (r4_wellord1(X0,k1_wellord2(sK5)) | ~r4_wellord1(X0,k1_wellord2(sK4)) | ~v1_relat_1(k1_wellord2(sK4)) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f178,f63])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    ( ! [X0] : (r4_wellord1(X0,k1_wellord2(sK5)) | ~r4_wellord1(X0,k1_wellord2(sK4)) | ~v1_relat_1(k1_wellord2(sK5)) | ~v1_relat_1(k1_wellord2(sK4)) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(resolution,[],[f66,f61])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r4_wellord1(X1,X2) | r4_wellord1(X0,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((r4_wellord1(X0,X2) | (~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r4_wellord1(X1,X2) & r4_wellord1(X0,X1)) => r4_wellord1(X0,X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).
% 0.22/0.54  fof(f736,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK5)) | ~r2_hidden(sK5,k3_relat_1(k1_wellord2(sK5))) | (~spl8_1 | ~spl8_9 | spl8_10)),
% 0.22/0.54    inference(forward_demodulation,[],[f735,f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X0] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0)) )),
% 0.22/0.54    inference(resolution,[],[f84,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.54  fof(f735,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK5)) | ~r2_hidden(sK5,k3_relat_1(k1_wellord2(sK5))) | (~spl8_1 | ~spl8_9 | spl8_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f734,f63])).
% 0.22/0.54  fof(f734,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK5)) | ~r2_hidden(sK5,k3_relat_1(k1_wellord2(sK5))) | ~v1_relat_1(k1_wellord2(sK5)) | (~spl8_1 | ~spl8_9 | spl8_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f733,f711])).
% 0.22/0.54  fof(f711,plain,(
% 0.22/0.54    v2_wellord1(k1_wellord2(sK5)) | ~spl8_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f710])).
% 0.22/0.54  fof(f710,plain,(
% 0.22/0.54    spl8_9 <=> v2_wellord1(k1_wellord2(sK5))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.54  fof(f733,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK5)) | ~r2_hidden(sK5,k3_relat_1(k1_wellord2(sK5))) | ~v2_wellord1(k1_wellord2(sK5)) | ~v1_relat_1(k1_wellord2(sK5)) | (~spl8_1 | spl8_10)),
% 0.22/0.54    inference(superposition,[],[f64,f729])).
% 0.22/0.54  fof(f729,plain,(
% 0.22/0.54    sK5 = k1_wellord1(k1_wellord2(sK5),sK5) | (~spl8_1 | spl8_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f728,f60])).
% 0.22/0.54  fof(f728,plain,(
% 0.22/0.54    ~v3_ordinal1(sK5) | sK5 = k1_wellord1(k1_wellord2(sK5),sK5) | (~spl8_1 | spl8_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f723,f62])).
% 0.22/0.54  fof(f723,plain,(
% 0.22/0.54    sK4 = sK5 | ~v3_ordinal1(sK5) | sK5 = k1_wellord1(k1_wellord2(sK5),sK5) | (~spl8_1 | spl8_10)),
% 0.22/0.54    inference(resolution,[],[f716,f612])).
% 0.22/0.54  fof(f612,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK4,X0) | sK4 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK5),X0) = X0) ) | ~spl8_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f610,f60])).
% 0.22/0.54  fof(f610,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK4,X0) | sK4 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK5),X0) = X0 | ~v3_ordinal1(sK5)) ) | ~spl8_1),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f606])).
% 0.22/0.54  fof(f606,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK4,X0) | sK4 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK5),X0) = X0 | ~v3_ordinal1(sK5) | ~v3_ordinal1(X0)) ) | ~spl8_1),
% 0.22/0.54    inference(resolution,[],[f593,f68])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.22/0.54  fof(f720,plain,(
% 0.22/0.54    spl8_9),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f719])).
% 0.22/0.54  fof(f719,plain,(
% 0.22/0.54    $false | spl8_9),
% 0.22/0.54    inference(subsumption_resolution,[],[f718,f60])).
% 0.22/0.54  fof(f718,plain,(
% 0.22/0.54    ~v3_ordinal1(sK5) | spl8_9),
% 0.22/0.54    inference(resolution,[],[f712,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.22/0.54  fof(f712,plain,(
% 0.22/0.54    ~v2_wellord1(k1_wellord2(sK5)) | spl8_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f710])).
% 0.22/0.54  fof(f717,plain,(
% 0.22/0.54    ~spl8_9 | ~spl8_10 | ~spl8_1 | ~spl8_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f708,f700,f290,f714,f710])).
% 0.22/0.54  fof(f708,plain,(
% 0.22/0.54    ~r2_hidden(sK4,sK5) | ~v2_wellord1(k1_wellord2(sK5)) | (~spl8_1 | ~spl8_8)),
% 0.22/0.54    inference(forward_demodulation,[],[f707,f99])).
% 0.22/0.54  % (23903)Refutation not found, incomplete strategy% (23903)------------------------------
% 0.22/0.54  % (23903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23903)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23903)Memory used [KB]: 10618
% 0.22/0.54  % (23903)Time elapsed: 0.119 s
% 0.22/0.54  % (23903)------------------------------
% 0.22/0.54  % (23903)------------------------------
% 0.22/0.54  fof(f707,plain,(
% 0.22/0.54    ~r2_hidden(sK4,k3_relat_1(k1_wellord2(sK5))) | ~v2_wellord1(k1_wellord2(sK5)) | (~spl8_1 | ~spl8_8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f706,f105])).
% 0.22/0.54  fof(f706,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) | ~r2_hidden(sK4,k3_relat_1(k1_wellord2(sK5))) | ~v2_wellord1(k1_wellord2(sK5)) | (~spl8_1 | ~spl8_8)),
% 0.22/0.54    inference(forward_demodulation,[],[f705,f292])).
% 0.22/0.54  fof(f705,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK4)) | ~r2_hidden(sK4,k3_relat_1(k1_wellord2(sK5))) | ~v2_wellord1(k1_wellord2(sK5)) | ~spl8_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f704,f63])).
% 0.22/0.54  fof(f704,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK4)) | ~r2_hidden(sK4,k3_relat_1(k1_wellord2(sK5))) | ~v2_wellord1(k1_wellord2(sK5)) | ~v1_relat_1(k1_wellord2(sK5)) | ~spl8_8),
% 0.22/0.54    inference(superposition,[],[f64,f702])).
% 0.22/0.54  fof(f702,plain,(
% 0.22/0.54    sK4 = k1_wellord1(k1_wellord2(sK5),sK4) | ~spl8_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f700])).
% 0.22/0.54  fof(f519,plain,(
% 0.22/0.54    ~spl8_2 | ~spl8_5 | spl8_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f518])).
% 0.22/0.54  fof(f518,plain,(
% 0.22/0.54    $false | (~spl8_2 | ~spl8_5 | spl8_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f517,f59])).
% 0.22/0.54  fof(f517,plain,(
% 0.22/0.54    ~v3_ordinal1(sK4) | (~spl8_2 | ~spl8_5 | spl8_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f516,f62])).
% 0.22/0.54  fof(f516,plain,(
% 0.22/0.54    sK4 = sK5 | ~v3_ordinal1(sK4) | (~spl8_2 | ~spl8_5 | spl8_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f512,f490])).
% 0.22/0.54  fof(f490,plain,(
% 0.22/0.54    ~r2_hidden(sK4,sK4) | spl8_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f488])).
% 0.22/0.54  fof(f512,plain,(
% 0.22/0.54    r2_hidden(sK4,sK4) | sK4 = sK5 | ~v3_ordinal1(sK4) | (~spl8_2 | ~spl8_5 | spl8_6)),
% 0.22/0.54    inference(resolution,[],[f508,f365])).
% 0.22/0.54  fof(f365,plain,(
% 0.22/0.54    ( ! [X7] : (r2_hidden(sK5,X7) | r2_hidden(X7,sK4) | sK5 = X7 | ~v3_ordinal1(X7)) ) | ~spl8_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f358,f60])).
% 0.22/0.54  fof(f358,plain,(
% 0.22/0.54    ( ! [X7] : (r2_hidden(X7,sK4) | r2_hidden(sK5,X7) | sK5 = X7 | ~v3_ordinal1(sK5) | ~v3_ordinal1(X7)) ) | ~spl8_2),
% 0.22/0.54    inference(resolution,[],[f320,f69])).
% 0.22/0.54  fof(f320,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,sK5) | r2_hidden(X2,sK4)) ) | ~spl8_2),
% 0.22/0.54    inference(forward_demodulation,[],[f319,f99])).
% 0.22/0.54  fof(f319,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,sK5) | r2_hidden(X2,k3_relat_1(k1_wellord2(sK4)))) ) | ~spl8_2),
% 0.22/0.54    inference(forward_demodulation,[],[f318,f99])).
% 0.22/0.54  fof(f318,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,k3_relat_1(k1_wellord2(sK5))) | r2_hidden(X2,k3_relat_1(k1_wellord2(sK4)))) ) | ~spl8_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f301,f63])).
% 0.22/0.54  fof(f301,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,k3_relat_1(k1_wellord2(sK5))) | r2_hidden(X2,k3_relat_1(k1_wellord2(sK4))) | ~v1_relat_1(k1_wellord2(sK4))) ) | ~spl8_2),
% 0.22/0.54    inference(superposition,[],[f91,f296])).
% 0.22/0.54  fof(f296,plain,(
% 0.22/0.54    k1_wellord2(sK5) = k2_wellord1(k1_wellord2(sK4),sK5) | ~spl8_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f294])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    spl8_2 <=> k1_wellord2(sK5) = k2_wellord1(k1_wellord2(sK4),sK5)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.54  fof(f508,plain,(
% 0.22/0.54    ~r2_hidden(sK5,sK4) | (~spl8_2 | ~spl8_5 | spl8_6)),
% 0.22/0.54    inference(forward_demodulation,[],[f507,f99])).
% 0.22/0.54  fof(f507,plain,(
% 0.22/0.54    ~r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4))) | (~spl8_2 | ~spl8_5 | spl8_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f506,f61])).
% 0.22/0.54  fof(f506,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) | ~r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4))) | (~spl8_2 | ~spl8_5 | spl8_6)),
% 0.22/0.54    inference(forward_demodulation,[],[f505,f296])).
% 0.22/0.54  fof(f505,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK5)) | ~r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4))) | (~spl8_2 | ~spl8_5 | spl8_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f504,f63])).
% 0.22/0.54  fof(f504,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK5)) | ~r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4))) | ~v1_relat_1(k1_wellord2(sK4)) | (~spl8_2 | ~spl8_5 | spl8_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f503,f485])).
% 0.22/0.54  fof(f485,plain,(
% 0.22/0.54    v2_wellord1(k1_wellord2(sK4)) | ~spl8_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f484])).
% 0.22/0.54  fof(f484,plain,(
% 0.22/0.54    spl8_5 <=> v2_wellord1(k1_wellord2(sK4))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.54  fof(f503,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK5)) | ~r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4))) | ~v2_wellord1(k1_wellord2(sK4)) | ~v1_relat_1(k1_wellord2(sK4)) | (~spl8_2 | spl8_6)),
% 0.22/0.54    inference(superposition,[],[f64,f502])).
% 0.22/0.54  fof(f502,plain,(
% 0.22/0.54    sK5 = k1_wellord1(k1_wellord2(sK4),sK5) | (~spl8_2 | spl8_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f501,f59])).
% 0.22/0.54  fof(f501,plain,(
% 0.22/0.54    ~v3_ordinal1(sK4) | sK5 = k1_wellord1(k1_wellord2(sK4),sK5) | (~spl8_2 | spl8_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f495,f62])).
% 0.22/0.54  fof(f495,plain,(
% 0.22/0.54    sK4 = sK5 | ~v3_ordinal1(sK4) | sK5 = k1_wellord1(k1_wellord2(sK4),sK5) | (~spl8_2 | spl8_6)),
% 0.22/0.54    inference(resolution,[],[f490,f364])).
% 0.22/0.54  fof(f364,plain,(
% 0.22/0.54    ( ! [X6] : (r2_hidden(X6,sK4) | sK5 = X6 | ~v3_ordinal1(X6) | sK5 = k1_wellord1(k1_wellord2(X6),sK5)) ) | ~spl8_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f357,f60])).
% 0.22/0.54  fof(f357,plain,(
% 0.22/0.54    ( ! [X6] : (r2_hidden(X6,sK4) | sK5 = X6 | ~v3_ordinal1(sK5) | ~v3_ordinal1(X6) | sK5 = k1_wellord1(k1_wellord2(X6),sK5)) ) | ~spl8_2),
% 0.22/0.54    inference(resolution,[],[f320,f169])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ( ! [X6,X7] : (r2_hidden(X7,X6) | X6 = X7 | ~v3_ordinal1(X6) | ~v3_ordinal1(X7) | k1_wellord1(k1_wellord2(X7),X6) = X6) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f158])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    ( ! [X6,X7] : (r2_hidden(X7,X6) | X6 = X7 | ~v3_ordinal1(X6) | ~v3_ordinal1(X7) | k1_wellord1(k1_wellord2(X7),X6) = X6 | ~v3_ordinal1(X7) | ~v3_ordinal1(X6)) )),
% 0.22/0.54    inference(resolution,[],[f69,f68])).
% 0.22/0.54  fof(f494,plain,(
% 0.22/0.54    spl8_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f493])).
% 0.22/0.54  fof(f493,plain,(
% 0.22/0.54    $false | spl8_5),
% 0.22/0.54    inference(subsumption_resolution,[],[f492,f59])).
% 0.22/0.54  fof(f492,plain,(
% 0.22/0.54    ~v3_ordinal1(sK4) | spl8_5),
% 0.22/0.54    inference(resolution,[],[f486,f67])).
% 0.22/0.54  fof(f486,plain,(
% 0.22/0.54    ~v2_wellord1(k1_wellord2(sK4)) | spl8_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f484])).
% 0.22/0.54  fof(f491,plain,(
% 0.22/0.54    ~spl8_5 | ~spl8_6 | ~spl8_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f482,f470,f488,f484])).
% 0.22/0.54  fof(f482,plain,(
% 0.22/0.54    ~r2_hidden(sK4,sK4) | ~v2_wellord1(k1_wellord2(sK4)) | ~spl8_3),
% 0.22/0.54    inference(forward_demodulation,[],[f481,f99])).
% 0.22/0.54  fof(f481,plain,(
% 0.22/0.54    ~r2_hidden(sK4,k3_relat_1(k1_wellord2(sK4))) | ~v2_wellord1(k1_wellord2(sK4)) | ~spl8_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f480,f192])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK4))),
% 0.22/0.54    inference(subsumption_resolution,[],[f190,f63])).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK4)) | ~v1_relat_1(k1_wellord2(sK4))),
% 0.22/0.54    inference(resolution,[],[f183,f61])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    ( ! [X1] : (~r4_wellord1(X1,k1_wellord2(sK5)) | r4_wellord1(X1,k1_wellord2(sK4)) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f182,f63])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    ( ! [X1] : (r4_wellord1(X1,k1_wellord2(sK4)) | ~r4_wellord1(X1,k1_wellord2(sK5)) | ~v1_relat_1(k1_wellord2(sK5)) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f179,f63])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    ( ! [X1] : (r4_wellord1(X1,k1_wellord2(sK4)) | ~r4_wellord1(X1,k1_wellord2(sK5)) | ~v1_relat_1(k1_wellord2(sK4)) | ~v1_relat_1(k1_wellord2(sK5)) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(resolution,[],[f66,f105])).
% 0.22/0.54  fof(f480,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK4)) | ~r2_hidden(sK4,k3_relat_1(k1_wellord2(sK4))) | ~v2_wellord1(k1_wellord2(sK4)) | ~spl8_3),
% 0.22/0.54    inference(forward_demodulation,[],[f479,f109])).
% 0.22/0.54  fof(f479,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK4)) | ~r2_hidden(sK4,k3_relat_1(k1_wellord2(sK4))) | ~v2_wellord1(k1_wellord2(sK4)) | ~spl8_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f478,f63])).
% 0.22/0.54  fof(f478,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK4)) | ~r2_hidden(sK4,k3_relat_1(k1_wellord2(sK4))) | ~v2_wellord1(k1_wellord2(sK4)) | ~v1_relat_1(k1_wellord2(sK4)) | ~spl8_3),
% 0.22/0.54    inference(superposition,[],[f64,f472])).
% 0.22/0.54  fof(f472,plain,(
% 0.22/0.54    sK4 = k1_wellord1(k1_wellord2(sK4),sK4) | ~spl8_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f470])).
% 0.22/0.54  fof(f297,plain,(
% 0.22/0.54    spl8_1 | spl8_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f287,f294,f290])).
% 0.22/0.54  fof(f287,plain,(
% 0.22/0.54    k1_wellord2(sK5) = k2_wellord1(k1_wellord2(sK4),sK5) | k1_wellord2(sK4) = k2_wellord1(k1_wellord2(sK5),sK4)),
% 0.22/0.54    inference(resolution,[],[f284,f60])).
% 0.22/0.54  fof(f284,plain,(
% 0.22/0.54    ( ! [X0] : (~v3_ordinal1(X0) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(sK4),X0) | k1_wellord2(sK4) = k2_wellord1(k1_wellord2(X0),sK4)) )),
% 0.22/0.54    inference(resolution,[],[f173,f59])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~v3_ordinal1(X3) | ~v3_ordinal1(X2) | k1_wellord2(X2) = k2_wellord1(k1_wellord2(X3),X2) | k1_wellord2(X3) = k2_wellord1(k1_wellord2(X2),X3)) )),
% 0.22/0.54    inference(resolution,[],[f123,f84])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r1_tarski(X3,X2) | ~v3_ordinal1(X2) | ~v3_ordinal1(X3) | k1_wellord2(X2) = k2_wellord1(k1_wellord2(X3),X2)) )),
% 0.22/0.54    inference(resolution,[],[f121,f84])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f120])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(resolution,[],[f117,f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(resolution,[],[f86,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (23927)------------------------------
% 0.22/0.54  % (23927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23927)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (23927)Memory used [KB]: 11129
% 0.22/0.54  % (23927)Time elapsed: 0.112 s
% 0.22/0.54  % (23927)------------------------------
% 0.22/0.54  % (23927)------------------------------
% 0.22/0.54  % (23901)Success in time 0.182 s
%------------------------------------------------------------------------------
