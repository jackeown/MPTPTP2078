%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 (  93 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :  149 ( 248 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f34,f38,f42,f46,f50,f77,f90,f107,f117,f122])).

fof(f122,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f118,f33])).

fof(f33,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f118,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_1
    | ~ spl4_20 ),
    inference(resolution,[],[f116,f23])).

fof(f23,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl4_1
  <=> r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f116,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X2,sK2),k2_zfmisc_1(X3,sK3))
        | ~ r1_tarski(X2,X3) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_20
  <=> ! [X3,X2] :
        ( r1_tarski(k2_zfmisc_1(X2,sK2),k2_zfmisc_1(X3,sK3))
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f117,plain,
    ( spl4_20
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f109,f105,f44,f115])).

fof(f44,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f105,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK3),X1)
        | r1_tarski(k2_zfmisc_1(X0,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f109,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X2,sK2),k2_zfmisc_1(X3,sK3))
        | ~ r1_tarski(X2,X3) )
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(resolution,[],[f106,f45])).

fof(f45,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK3),X1)
        | r1_tarski(k2_zfmisc_1(X0,sK2),X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl4_18
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f103,f88,f48,f105])).

fof(f48,plain,
    ( spl4_7
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f88,plain,
    ( spl4_14
  <=> ! [X0] : k2_zfmisc_1(X0,sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK3),X1)
        | r1_tarski(k2_zfmisc_1(X0,sK2),X1) )
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(superposition,[],[f49,f89])).

fof(f89,plain,
    ( ! [X0] : k2_zfmisc_1(X0,sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X0,sK3))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f88])).

fof(f49,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f90,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f83,f75,f26,f88])).

fof(f26,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

% (29788)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
fof(f75,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f83,plain,
    ( ! [X0] : k2_zfmisc_1(X0,sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X0,sK3))
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(resolution,[],[f76,f28])).

fof(f28,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,
    ( spl4_12
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f73,f40,f36,f75])).

fof(f36,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f40,plain,
    ( spl4_5
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f41,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f50,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f46,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f42,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f34,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f13,f31])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f29,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f15,f21])).

fof(f15,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (29786)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.42  % (29791)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (29791)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f123,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f24,f29,f34,f38,f42,f46,f50,f77,f90,f107,f117,f122])).
% 0.20/0.42  fof(f122,plain,(
% 0.20/0.42    spl4_1 | ~spl4_3 | ~spl4_20),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f121])).
% 0.20/0.42  fof(f121,plain,(
% 0.20/0.42    $false | (spl4_1 | ~spl4_3 | ~spl4_20)),
% 0.20/0.42    inference(subsumption_resolution,[],[f118,f33])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.42  fof(f118,plain,(
% 0.20/0.42    ~r1_tarski(sK0,sK1) | (spl4_1 | ~spl4_20)),
% 0.20/0.42    inference(resolution,[],[f116,f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) | spl4_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    spl4_1 <=> r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.42  fof(f116,plain,(
% 0.20/0.42    ( ! [X2,X3] : (r1_tarski(k2_zfmisc_1(X2,sK2),k2_zfmisc_1(X3,sK3)) | ~r1_tarski(X2,X3)) ) | ~spl4_20),
% 0.20/0.42    inference(avatar_component_clause,[],[f115])).
% 0.20/0.42  fof(f115,plain,(
% 0.20/0.42    spl4_20 <=> ! [X3,X2] : (r1_tarski(k2_zfmisc_1(X2,sK2),k2_zfmisc_1(X3,sK3)) | ~r1_tarski(X2,X3))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.42  fof(f117,plain,(
% 0.20/0.42    spl4_20 | ~spl4_6 | ~spl4_18),
% 0.20/0.42    inference(avatar_split_clause,[],[f109,f105,f44,f115])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    spl4_6 <=> ! [X1,X0,X2] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.42  fof(f105,plain,(
% 0.20/0.42    spl4_18 <=> ! [X1,X0] : (~r1_tarski(k2_zfmisc_1(X0,sK3),X1) | r1_tarski(k2_zfmisc_1(X0,sK2),X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.42  fof(f109,plain,(
% 0.20/0.42    ( ! [X2,X3] : (r1_tarski(k2_zfmisc_1(X2,sK2),k2_zfmisc_1(X3,sK3)) | ~r1_tarski(X2,X3)) ) | (~spl4_6 | ~spl4_18)),
% 0.20/0.42    inference(resolution,[],[f106,f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) ) | ~spl4_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f44])).
% 0.20/0.42  fof(f106,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,sK3),X1) | r1_tarski(k2_zfmisc_1(X0,sK2),X1)) ) | ~spl4_18),
% 0.20/0.42    inference(avatar_component_clause,[],[f105])).
% 0.20/0.42  fof(f107,plain,(
% 0.20/0.42    spl4_18 | ~spl4_7 | ~spl4_14),
% 0.20/0.42    inference(avatar_split_clause,[],[f103,f88,f48,f105])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    spl4_7 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    spl4_14 <=> ! [X0] : k2_zfmisc_1(X0,sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X0,sK3))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.42  fof(f103,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,sK3),X1) | r1_tarski(k2_zfmisc_1(X0,sK2),X1)) ) | (~spl4_7 | ~spl4_14)),
% 0.20/0.42    inference(superposition,[],[f49,f89])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    ( ! [X0] : (k2_zfmisc_1(X0,sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X0,sK3))) ) | ~spl4_14),
% 0.20/0.42    inference(avatar_component_clause,[],[f88])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl4_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f48])).
% 0.20/0.42  fof(f90,plain,(
% 0.20/0.42    spl4_14 | ~spl4_2 | ~spl4_12),
% 0.20/0.42    inference(avatar_split_clause,[],[f83,f75,f26,f88])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    spl4_2 <=> r1_tarski(sK2,sK3)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.42  % (29788)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    spl4_12 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ( ! [X0] : (k2_zfmisc_1(X0,sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X0,sK3))) ) | (~spl4_2 | ~spl4_12)),
% 0.20/0.42    inference(resolution,[],[f76,f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f26])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ) | ~spl4_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f75])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    spl4_12 | ~spl4_4 | ~spl4_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f73,f40,f36,f75])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    spl4_4 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl4_5 <=> ! [X1,X0,X2] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ) | (~spl4_4 | ~spl4_5)),
% 0.20/0.42    inference(resolution,[],[f41,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f36])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl4_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f40])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    spl4_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f48])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl4_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f17,f44])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl4_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f40])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl4_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f36])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    spl4_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f13,f31])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f6])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.42    inference(negated_conjecture,[],[f4])).
% 0.20/0.42  fof(f4,conjecture,(
% 0.20/0.42    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    spl4_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f14,f26])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    r1_tarski(sK2,sK3)),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ~spl4_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f21])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (29791)------------------------------
% 0.20/0.42  % (29791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (29791)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (29791)Memory used [KB]: 10618
% 0.20/0.42  % (29791)Time elapsed: 0.006 s
% 0.20/0.42  % (29791)------------------------------
% 0.20/0.42  % (29791)------------------------------
% 0.20/0.42  % (29793)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (29785)Success in time 0.07 s
%------------------------------------------------------------------------------
