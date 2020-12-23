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
% DateTime   : Thu Dec  3 12:52:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 301 expanded)
%              Number of leaves         :   17 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  343 (1263 expanded)
%              Number of equality atoms :   63 ( 404 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f86,f91,f94,f106,f122,f151,f162,f167,f197])).

% (15294)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (15282)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (15300)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (15298)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (15293)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (15293)Refutation not found, incomplete strategy% (15293)------------------------------
% (15293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15292)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f197,plain,
    ( spl1_2
    | ~ spl1_3
    | ~ spl1_10 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl1_2
    | ~ spl1_3
    | ~ spl1_10 ),
    inference(subsumption_resolution,[],[f195,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f195,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl1_2
    | ~ spl1_3
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f194,f117])).

fof(f117,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl1_10
  <=> k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f194,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f193,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f193,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f189,f62])).

fof(f62,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl1_3
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f189,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_2 ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_2 ),
    inference(superposition,[],[f46,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f46,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

% (15303)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f167,plain,
    ( spl1_10
    | ~ spl1_4
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f166,f111,f65,f115])).

fof(f65,plain,
    ( spl1_4
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f111,plain,
    ( spl1_9
  <=> r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f166,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ spl1_4
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f163,f66])).

fof(f66,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f163,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | ~ spl1_9 ),
    inference(resolution,[],[f112,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f112,plain,
    ( r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f162,plain,(
    spl1_9 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl1_9 ),
    inference(subsumption_resolution,[],[f160,f24])).

fof(f160,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_9 ),
    inference(subsumption_resolution,[],[f159,f25])).

fof(f25,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f159,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_9 ),
    inference(subsumption_resolution,[],[f158,f26])).

fof(f26,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f158,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_9 ),
    inference(subsumption_resolution,[],[f153,f37])).

fof(f153,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_9 ),
    inference(superposition,[],[f113,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f113,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | spl1_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f151,plain,(
    spl1_8 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl1_8 ),
    inference(subsumption_resolution,[],[f149,f24])).

fof(f149,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_8 ),
    inference(subsumption_resolution,[],[f148,f25])).

fof(f148,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_8 ),
    inference(subsumption_resolution,[],[f147,f26])).

fof(f147,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_8 ),
    inference(trivial_inequality_removal,[],[f146])).

fof(f146,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_8 ),
    inference(superposition,[],[f85,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f32,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f32,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | spl1_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl1_8
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f122,plain,
    ( spl1_7
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f121,f65,f79])).

fof(f79,plain,
    ( spl1_7
  <=> r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f121,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f120,f24])).

fof(f120,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f119,f25])).

fof(f119,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f108,f26])).

fof(f108,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(superposition,[],[f66,f31])).

fof(f106,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl1_4 ),
    inference(subsumption_resolution,[],[f104,f24])).

fof(f104,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(subsumption_resolution,[],[f103,f25])).

fof(f103,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(subsumption_resolution,[],[f102,f26])).

fof(f102,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f97,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(superposition,[],[f67,f33])).

fof(f67,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f94,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl1_6 ),
    inference(subsumption_resolution,[],[f92,f24])).

fof(f92,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(resolution,[],[f77,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (15285)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f77,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl1_6
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f91,plain,
    ( ~ spl1_6
    | spl1_3 ),
    inference(avatar_split_clause,[],[f90,f61,f75])).

fof(f90,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_3 ),
    inference(subsumption_resolution,[],[f89,f24])).

fof(f89,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f88,f25])).

fof(f88,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f87,f26])).

fof(f87,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(superposition,[],[f63,f31])).

fof(f63,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f86,plain,
    ( ~ spl1_6
    | ~ spl1_7
    | ~ spl1_8
    | spl1_1 ),
    inference(avatar_split_clause,[],[f73,f40,f83,f79,f75])).

fof(f40,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f73,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_1 ),
    inference(subsumption_resolution,[],[f58,f24])).

fof(f58,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_1 ),
    inference(superposition,[],[f52,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f52,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl1_1 ),
    inference(subsumption_resolution,[],[f51,f24])).

fof(f51,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(subsumption_resolution,[],[f50,f25])).

fof(f50,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(subsumption_resolution,[],[f49,f26])).

fof(f49,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(superposition,[],[f42,f31])).

fof(f42,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f47,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f27,f44,f40])).

fof(f27,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:29:22 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.51  % (15284)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (15281)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (15284)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f47,f86,f91,f94,f106,f122,f151,f162,f167,f197])).
% 0.22/0.52  % (15294)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (15282)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (15300)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (15298)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (15293)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (15293)Refutation not found, incomplete strategy% (15293)------------------------------
% 0.22/0.52  % (15293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15292)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    spl1_2 | ~spl1_3 | ~spl1_10),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f196])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    $false | (spl1_2 | ~spl1_3 | ~spl1_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f195,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | (spl1_2 | ~spl1_3 | ~spl1_10)),
% 0.22/0.52    inference(forward_demodulation,[],[f194,f117])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) | ~spl1_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f115])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    spl1_10 <=> k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | (spl1_2 | ~spl1_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f193,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f7])).
% 0.22/0.52  fof(f7,conjecture,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f189,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    v1_relat_1(k2_funct_1(sK0)) | ~spl1_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl1_3 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | spl1_2),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f188])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k2_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | spl1_2),
% 0.22/0.52    inference(superposition,[],[f46,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    spl1_2 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.52  % (15303)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    spl1_10 | ~spl1_4 | ~spl1_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f166,f111,f65,f115])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    spl1_4 <=> r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    spl1_9 <=> r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) | (~spl1_4 | ~spl1_9)),
% 0.22/0.52    inference(subsumption_resolution,[],[f163,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) | ~spl1_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f65])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) | ~spl1_9),
% 0.22/0.52    inference(resolution,[],[f112,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | ~spl1_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f111])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    spl1_9),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f161])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    $false | spl1_9),
% 0.22/0.52    inference(subsumption_resolution,[],[f160,f24])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    ~v1_relat_1(sK0) | spl1_9),
% 0.22/0.52    inference(subsumption_resolution,[],[f159,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    v1_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_9),
% 0.22/0.52    inference(subsumption_resolution,[],[f158,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    v2_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_9),
% 0.22/0.52    inference(subsumption_resolution,[],[f153,f37])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_9),
% 0.22/0.52    inference(superposition,[],[f113,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | spl1_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f111])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    spl1_8),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f150])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    $false | spl1_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f149,f24])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ~v1_relat_1(sK0) | spl1_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f148,f25])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f147,f26])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_8),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f146])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k2_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_8),
% 0.22/0.52    inference(superposition,[],[f85,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(superposition,[],[f32,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | spl1_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl1_8 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    spl1_7 | ~spl1_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f121,f65,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl1_7 <=> r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) | ~spl1_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f120,f24])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f119,f25])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f108,f26])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.22/0.52    inference(superposition,[],[f66,f31])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    spl1_4),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f105])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    $false | spl1_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f104,f24])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ~v1_relat_1(sK0) | spl1_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f103,f25])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f102,f26])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f97,f37])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_4),
% 0.22/0.52    inference(superposition,[],[f67,f33])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) | spl1_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f65])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    spl1_6),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    $false | spl1_6),
% 0.22/0.52    inference(subsumption_resolution,[],[f92,f24])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ~v1_relat_1(sK0) | spl1_6),
% 0.22/0.52    inference(resolution,[],[f77,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  % (15285)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(sK0)) | spl1_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl1_6 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ~spl1_6 | spl1_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f90,f61,f75])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(sK0)) | spl1_3),
% 0.22/0.52    inference(subsumption_resolution,[],[f89,f24])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_3),
% 0.22/0.52    inference(subsumption_resolution,[],[f88,f25])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 0.22/0.52    inference(subsumption_resolution,[],[f87,f26])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 0.22/0.52    inference(superposition,[],[f63,f31])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK0)) | spl1_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f61])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ~spl1_6 | ~spl1_7 | ~spl1_8 | spl1_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f73,f40,f83,f79,f75])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    spl1_1 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | spl1_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f58,f24])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | spl1_1),
% 0.22/0.52    inference(superposition,[],[f52,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | spl1_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f51,f24])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | ~v1_relat_1(sK0) | spl1_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f50,f25])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f49,f26])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_1),
% 0.22/0.52    inference(superposition,[],[f42,f31])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f40])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ~spl1_1 | ~spl1_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f44,f40])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (15284)------------------------------
% 0.22/0.52  % (15284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15284)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (15284)Memory used [KB]: 6140
% 0.22/0.52  % (15284)Time elapsed: 0.087 s
% 0.22/0.52  % (15284)------------------------------
% 0.22/0.52  % (15284)------------------------------
% 0.22/0.52  % (15293)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15293)Memory used [KB]: 6140
% 0.22/0.52  % (15293)Time elapsed: 0.104 s
% 0.22/0.52  % (15293)------------------------------
% 0.22/0.52  % (15293)------------------------------
% 0.22/0.53  % (15279)Success in time 0.157 s
%------------------------------------------------------------------------------
