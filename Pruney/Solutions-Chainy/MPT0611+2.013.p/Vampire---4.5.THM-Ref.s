%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 127 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  201 ( 382 expanded)
%              Number of equality atoms :   21 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f45,f49,f57,f61,f65,f82,f87,f97,f103,f143,f196,f219])).

fof(f219,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_33 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f217,f44])).

fof(f44,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f217,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_1
    | ~ spl2_12
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f212,f29])).

fof(f29,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f212,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl2_12
    | ~ spl2_33 ),
    inference(superposition,[],[f81,f195])).

fof(f195,plain,
    ( ! [X2] : sK1 = k4_xboole_0(sK1,k2_zfmisc_1(X2,k2_relat_1(sK0)))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl2_33
  <=> ! [X2] : sK1 = k4_xboole_0(sK1,k2_zfmisc_1(X2,k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_relat_1(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | r1_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f196,plain,
    ( spl2_33
    | ~ spl2_16
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f184,f141,f101,f194])).

fof(f101,plain,
    ( spl2_16
  <=> ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f141,plain,
    ( spl2_23
  <=> ! [X16,X17] : k2_zfmisc_1(X16,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X16,k2_relat_1(sK0)),k2_zfmisc_1(X17,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f184,plain,
    ( ! [X2] : sK1 = k4_xboole_0(sK1,k2_zfmisc_1(X2,k2_relat_1(sK0)))
    | ~ spl2_16
    | ~ spl2_23 ),
    inference(superposition,[],[f102,f142])).

fof(f142,plain,
    ( ! [X17,X16] : k2_zfmisc_1(X16,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X16,k2_relat_1(sK0)),k2_zfmisc_1(X17,k2_relat_1(sK1)))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f141])).

fof(f102,plain,
    ( ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f143,plain,
    ( spl2_23
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f125,f85,f32,f141])).

fof(f32,plain,
    ( spl2_2
  <=> r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( spl2_13
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f125,plain,
    ( ! [X17,X16] : k2_zfmisc_1(X16,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X16,k2_relat_1(sK0)),k2_zfmisc_1(X17,k2_relat_1(sK1)))
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(resolution,[],[f86,f34])).

fof(f34,plain,
    ( r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f86,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f103,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f98,f95,f37,f101])).

fof(f37,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f95,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f98,plain,
    ( ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(resolution,[],[f96,f39])).

fof(f39,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,
    ( spl2_15
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f93,f80,f55,f95])).

fof(f55,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 )
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(resolution,[],[f81,f56])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f87,plain,
    ( spl2_13
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f83,f63,f55,f85])).

fof(f63,plain,
    ( spl2_9
  <=> ! [X1,X3,X0,X2] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f83,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) )
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(resolution,[],[f64,f56])).

fof(f64,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f82,plain,
    ( spl2_12
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f78,f59,f47,f80])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r1_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f48,f60])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_xboole_0(X0,k4_xboole_0(X2,X1)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f48,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f65,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f23,f59])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f57,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).

fof(f40,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f27])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:53:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (20192)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (20191)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (20194)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (20193)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.44  % (20191)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f30,f35,f40,f45,f49,f57,f61,f65,f82,f87,f97,f103,f143,f196,f219])).
% 0.21/0.44  fof(f219,plain,(
% 0.21/0.44    spl2_1 | ~spl2_4 | ~spl2_12 | ~spl2_33),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f218])).
% 0.21/0.44  fof(f218,plain,(
% 0.21/0.44    $false | (spl2_1 | ~spl2_4 | ~spl2_12 | ~spl2_33)),
% 0.21/0.44    inference(subsumption_resolution,[],[f217,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    v1_relat_1(sK0) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl2_4 <=> v1_relat_1(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f217,plain,(
% 0.21/0.44    ~v1_relat_1(sK0) | (spl2_1 | ~spl2_12 | ~spl2_33)),
% 0.21/0.44    inference(subsumption_resolution,[],[f212,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f212,plain,(
% 0.21/0.44    r1_xboole_0(sK0,sK1) | ~v1_relat_1(sK0) | (~spl2_12 | ~spl2_33)),
% 0.21/0.44    inference(superposition,[],[f81,f195])).
% 0.21/0.44  fof(f195,plain,(
% 0.21/0.44    ( ! [X2] : (sK1 = k4_xboole_0(sK1,k2_zfmisc_1(X2,k2_relat_1(sK0)))) ) | ~spl2_33),
% 0.21/0.44    inference(avatar_component_clause,[],[f194])).
% 0.21/0.44  fof(f194,plain,(
% 0.21/0.44    spl2_33 <=> ! [X2] : sK1 = k4_xboole_0(sK1,k2_zfmisc_1(X2,k2_relat_1(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) ) | ~spl2_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f80])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    spl2_12 <=> ! [X1,X0] : (~v1_relat_1(X0) | r1_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.44  fof(f196,plain,(
% 0.21/0.44    spl2_33 | ~spl2_16 | ~spl2_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f184,f141,f101,f194])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    spl2_16 <=> ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    spl2_23 <=> ! [X16,X17] : k2_zfmisc_1(X16,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X16,k2_relat_1(sK0)),k2_zfmisc_1(X17,k2_relat_1(sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.44  fof(f184,plain,(
% 0.21/0.44    ( ! [X2] : (sK1 = k4_xboole_0(sK1,k2_zfmisc_1(X2,k2_relat_1(sK0)))) ) | (~spl2_16 | ~spl2_23)),
% 0.21/0.44    inference(superposition,[],[f102,f142])).
% 0.21/0.44  fof(f142,plain,(
% 0.21/0.44    ( ! [X17,X16] : (k2_zfmisc_1(X16,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X16,k2_relat_1(sK0)),k2_zfmisc_1(X17,k2_relat_1(sK1)))) ) | ~spl2_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f141])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))) ) | ~spl2_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f101])).
% 0.21/0.44  fof(f143,plain,(
% 0.21/0.44    spl2_23 | ~spl2_2 | ~spl2_13),
% 0.21/0.44    inference(avatar_split_clause,[],[f125,f85,f32,f141])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    spl2_2 <=> r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    spl2_13 <=> ! [X1,X3,X0,X2] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    ( ! [X17,X16] : (k2_zfmisc_1(X16,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X16,k2_relat_1(sK0)),k2_zfmisc_1(X17,k2_relat_1(sK1)))) ) | (~spl2_2 | ~spl2_13)),
% 0.21/0.44    inference(resolution,[],[f86,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f32])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))) ) | ~spl2_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f85])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    spl2_16 | ~spl2_3 | ~spl2_15),
% 0.21/0.44    inference(avatar_split_clause,[],[f98,f95,f37,f101])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    spl2_15 <=> ! [X1,X0] : (~v1_relat_1(X0) | k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))) ) | (~spl2_3 | ~spl2_15)),
% 0.21/0.44    inference(resolution,[],[f96,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    v1_relat_1(sK1) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f37])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) ) | ~spl2_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f95])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    spl2_15 | ~spl2_7 | ~spl2_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f93,f80,f55,f95])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl2_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) ) | (~spl2_7 | ~spl2_12)),
% 0.21/0.44    inference(resolution,[],[f81,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl2_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f55])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    spl2_13 | ~spl2_7 | ~spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f83,f63,f55,f85])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    spl2_9 <=> ! [X1,X3,X0,X2] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))) ) | (~spl2_7 | ~spl2_9)),
% 0.21/0.44    inference(resolution,[],[f64,f56])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) ) | ~spl2_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f63])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    spl2_12 | ~spl2_5 | ~spl2_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f78,f59,f47,f80])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl2_5 <=> ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    spl2_8 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) ) | (~spl2_5 | ~spl2_8)),
% 0.21/0.44    inference(resolution,[],[f48,f60])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) ) | ~spl2_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f59])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f47])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f63])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl2_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f59])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f55])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f47])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f42])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    v1_relat_1(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13,f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.44    inference(negated_conjecture,[],[f5])).
% 0.21/0.44  fof(f5,conjecture,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f32])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ~spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f27])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (20191)------------------------------
% 0.21/0.44  % (20191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (20191)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (20191)Memory used [KB]: 10618
% 0.21/0.44  % (20191)Time elapsed: 0.008 s
% 0.21/0.44  % (20191)------------------------------
% 0.21/0.44  % (20191)------------------------------
% 0.21/0.44  % (20185)Success in time 0.071 s
%------------------------------------------------------------------------------
