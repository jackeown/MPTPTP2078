%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:12 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 122 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  176 ( 383 expanded)
%              Number of equality atoms :   49 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f55,f60,f97,f125,f184,f233])).

fof(f233,plain,
    ( ~ spl4_6
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl4_6
    | spl4_9 ),
    inference(subsumption_resolution,[],[f229,f134])).

fof(f134,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f124,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f124,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_6
  <=> r2_hidden(sK0,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f229,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f183,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f183,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl4_9
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f184,plain,
    ( ~ spl4_9
    | spl4_2 ),
    inference(avatar_split_clause,[],[f99,f41,f181])).

fof(f41,plain,
    ( spl4_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f99,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f42,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_xboole_0
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f42,plain,
    ( sK0 != sK2
    | spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f125,plain,
    ( spl4_6
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f102,f37,f122])).

fof(f37,plain,
    ( spl4_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f102,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f39,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f97,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f95,f77])).

fof(f77,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1)))
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f25])).

% (6915)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f95,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f90,f54])).

fof(f54,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_3
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f90,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl4_4 ),
    inference(resolution,[],[f33,f59])).

fof(f59,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_4
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,
    ( ~ spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f49,f41,f57])).

fof(f49,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f48,f43])).

fof(f43,plain,
    ( sK0 = sK2
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f48,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))
    | sK0 != sK2
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f46,f47])).

fof(f47,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f45,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))
    | r2_hidden(sK1,sK3)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f22,f43])).

fof(f22,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r2_hidden(sK1,sK3)
      | sK0 != sK2
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) )
    & ( ( r2_hidden(sK1,sK3)
        & sK0 = sK2 )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).

% (6909)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(X1,X3)
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
        & ( ( r2_hidden(X1,X3)
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) )
   => ( ( ~ r2_hidden(sK1,sK3)
        | sK0 != sK2
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) )
      & ( ( r2_hidden(sK1,sK3)
          & sK0 = sK2 )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f46,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))
    | ~ r2_hidden(sK1,sK3)
    | sK0 != sK2
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f23,f43])).

fof(f23,plain,
    ( ~ r2_hidden(sK1,sK3)
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f47,f41,f52])).

fof(f44,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f21,f41,f37])).

fof(f21,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:29:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.21/0.52  % (6921)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.21/0.52  % (6929)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.21/0.52  % (6914)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.21/0.52  % (6937)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.54  % (6929)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.33/0.54  % (6912)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.54  % (6913)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.33/0.54  % (6937)Refutation not found, incomplete strategy% (6937)------------------------------
% 1.33/0.54  % (6937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (6937)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (6937)Memory used [KB]: 10746
% 1.33/0.54  % (6937)Time elapsed: 0.128 s
% 1.33/0.54  % (6937)------------------------------
% 1.33/0.54  % (6937)------------------------------
% 1.33/0.54  % (6935)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % SZS output start Proof for theBenchmark
% 1.33/0.54  fof(f234,plain,(
% 1.33/0.54    $false),
% 1.33/0.54    inference(avatar_sat_refutation,[],[f44,f55,f60,f97,f125,f184,f233])).
% 1.33/0.54  fof(f233,plain,(
% 1.33/0.54    ~spl4_6 | spl4_9),
% 1.33/0.54    inference(avatar_contradiction_clause,[],[f232])).
% 1.33/0.54  fof(f232,plain,(
% 1.33/0.54    $false | (~spl4_6 | spl4_9)),
% 1.33/0.54    inference(subsumption_resolution,[],[f229,f134])).
% 1.33/0.54  fof(f134,plain,(
% 1.33/0.54    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) | ~spl4_6),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f124,f29])).
% 1.33/0.54  fof(f29,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f18])).
% 1.33/0.54  fof(f18,plain,(
% 1.33/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.33/0.54    inference(nnf_transformation,[],[f4])).
% 1.33/0.54  fof(f4,axiom,(
% 1.33/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.33/0.54  fof(f124,plain,(
% 1.33/0.54    r2_hidden(sK0,k1_tarski(sK2)) | ~spl4_6),
% 1.33/0.54    inference(avatar_component_clause,[],[f122])).
% 1.33/0.54  fof(f122,plain,(
% 1.33/0.54    spl4_6 <=> r2_hidden(sK0,k1_tarski(sK2))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.33/0.54  fof(f229,plain,(
% 1.33/0.54    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) | spl4_9),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f183,f26])).
% 1.33/0.54  fof(f26,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0) )),
% 1.33/0.54    inference(cnf_transformation,[],[f7])).
% 1.33/0.54  fof(f7,axiom,(
% 1.33/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 1.33/0.54  fof(f183,plain,(
% 1.33/0.54    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) | spl4_9),
% 1.33/0.54    inference(avatar_component_clause,[],[f181])).
% 1.33/0.54  fof(f181,plain,(
% 1.33/0.54    spl4_9 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.33/0.54  fof(f184,plain,(
% 1.33/0.54    ~spl4_9 | spl4_2),
% 1.33/0.54    inference(avatar_split_clause,[],[f99,f41,f181])).
% 1.33/0.54  fof(f41,plain,(
% 1.33/0.54    spl4_2 <=> sK0 = sK2),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.33/0.54  fof(f99,plain,(
% 1.33/0.54    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) | spl4_2),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f42,f28])).
% 1.33/0.54  fof(f28,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_xboole_0 | X0 = X1) )),
% 1.33/0.54    inference(cnf_transformation,[],[f13])).
% 1.33/0.54  fof(f13,plain,(
% 1.33/0.54    ! [X0,X1] : (X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_xboole_0)),
% 1.33/0.54    inference(ennf_transformation,[],[f6])).
% 1.33/0.54  fof(f6,axiom,(
% 1.33/0.54    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 => X0 = X1)),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 1.33/0.54  fof(f42,plain,(
% 1.33/0.54    sK0 != sK2 | spl4_2),
% 1.33/0.54    inference(avatar_component_clause,[],[f41])).
% 1.33/0.54  fof(f125,plain,(
% 1.33/0.54    spl4_6 | ~spl4_1),
% 1.33/0.54    inference(avatar_split_clause,[],[f102,f37,f122])).
% 1.33/0.54  fof(f37,plain,(
% 1.33/0.54    spl4_1 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.33/0.54  fof(f102,plain,(
% 1.33/0.54    r2_hidden(sK0,k1_tarski(sK2)) | ~spl4_1),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f39,f31])).
% 1.33/0.54  fof(f31,plain,(
% 1.33/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f20])).
% 1.33/0.54  fof(f20,plain,(
% 1.33/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.33/0.54    inference(flattening,[],[f19])).
% 1.33/0.54  fof(f19,plain,(
% 1.33/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.33/0.54    inference(nnf_transformation,[],[f5])).
% 1.33/0.54  fof(f5,axiom,(
% 1.33/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.33/0.54  fof(f39,plain,(
% 1.33/0.54    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) | ~spl4_1),
% 1.33/0.54    inference(avatar_component_clause,[],[f37])).
% 1.33/0.54  fof(f97,plain,(
% 1.33/0.54    ~spl4_3 | spl4_4),
% 1.33/0.54    inference(avatar_contradiction_clause,[],[f96])).
% 1.33/0.54  fof(f96,plain,(
% 1.33/0.54    $false | (~spl4_3 | spl4_4)),
% 1.33/0.54    inference(subsumption_resolution,[],[f95,f77])).
% 1.33/0.54  fof(f77,plain,(
% 1.33/0.54    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f34,f35])).
% 1.33/0.54  fof(f35,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k1_tarski(X1) != k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) | r2_hidden(X1,X0)) )),
% 1.33/0.54    inference(definition_unfolding,[],[f27,f25])).
% 1.33/0.54  fof(f25,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f2])).
% 1.33/0.54  fof(f2,axiom,(
% 1.33/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.33/0.54  fof(f27,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f12])).
% 1.33/0.54  fof(f12,plain,(
% 1.33/0.54    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 1.33/0.54    inference(ennf_transformation,[],[f3])).
% 1.33/0.54  fof(f3,axiom,(
% 1.33/0.54    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 1.33/0.54  fof(f34,plain,(
% 1.33/0.54    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.33/0.54    inference(definition_unfolding,[],[f24,f25])).
% 1.33/0.54  % (6915)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.54  fof(f24,plain,(
% 1.33/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.33/0.54    inference(cnf_transformation,[],[f10])).
% 1.33/0.54  fof(f10,plain,(
% 1.33/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.33/0.54    inference(rectify,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.33/0.54  fof(f95,plain,(
% 1.33/0.54    ~r2_hidden(sK0,k1_tarski(sK0)) | (~spl4_3 | spl4_4)),
% 1.33/0.54    inference(subsumption_resolution,[],[f90,f54])).
% 1.33/0.54  fof(f54,plain,(
% 1.33/0.54    r2_hidden(sK1,sK3) | ~spl4_3),
% 1.33/0.54    inference(avatar_component_clause,[],[f52])).
% 1.33/0.54  fof(f52,plain,(
% 1.33/0.54    spl4_3 <=> r2_hidden(sK1,sK3)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.33/0.54  fof(f90,plain,(
% 1.33/0.54    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK0,k1_tarski(sK0)) | spl4_4),
% 1.33/0.54    inference(resolution,[],[f33,f59])).
% 1.33/0.54  fof(f59,plain,(
% 1.33/0.54    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) | spl4_4),
% 1.33/0.54    inference(avatar_component_clause,[],[f57])).
% 1.33/0.54  fof(f57,plain,(
% 1.33/0.54    spl4_4 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.33/0.54  fof(f33,plain,(
% 1.33/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f20])).
% 1.33/0.54  fof(f60,plain,(
% 1.33/0.54    ~spl4_4 | ~spl4_2),
% 1.33/0.54    inference(avatar_split_clause,[],[f49,f41,f57])).
% 1.33/0.54  fof(f49,plain,(
% 1.33/0.54    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) | ~spl4_2),
% 1.33/0.54    inference(subsumption_resolution,[],[f48,f43])).
% 1.33/0.54  fof(f43,plain,(
% 1.33/0.54    sK0 = sK2 | ~spl4_2),
% 1.33/0.54    inference(avatar_component_clause,[],[f41])).
% 1.33/0.54  fof(f48,plain,(
% 1.33/0.54    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) | sK0 != sK2 | ~spl4_2),
% 1.33/0.54    inference(subsumption_resolution,[],[f46,f47])).
% 1.33/0.54  fof(f47,plain,(
% 1.33/0.54    r2_hidden(sK1,sK3) | ~spl4_2),
% 1.33/0.54    inference(subsumption_resolution,[],[f45,f32])).
% 1.33/0.54  fof(f32,plain,(
% 1.33/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f20])).
% 1.33/0.54  fof(f45,plain,(
% 1.33/0.54    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) | r2_hidden(sK1,sK3) | ~spl4_2),
% 1.33/0.54    inference(backward_demodulation,[],[f22,f43])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    r2_hidden(sK1,sK3) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.33/0.54    inference(cnf_transformation,[],[f17])).
% 1.33/0.54  fof(f17,plain,(
% 1.33/0.54    (~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))) & ((r2_hidden(sK1,sK3) & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).
% 1.33/0.54  % (6909)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.54  fof(f16,plain,(
% 1.33/0.54    ? [X0,X1,X2,X3] : ((~r2_hidden(X1,X3) | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)))) => ((~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))) & ((r2_hidden(sK1,sK3) & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f15,plain,(
% 1.33/0.54    ? [X0,X1,X2,X3] : ((~r2_hidden(X1,X3) | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.33/0.54    inference(flattening,[],[f14])).
% 1.33/0.54  fof(f14,plain,(
% 1.33/0.54    ? [X0,X1,X2,X3] : (((~r2_hidden(X1,X3) | X0 != X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.33/0.54    inference(nnf_transformation,[],[f11])).
% 1.33/0.54  fof(f11,plain,(
% 1.33/0.54    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <~> (r2_hidden(X1,X3) & X0 = X2))),
% 1.33/0.54    inference(ennf_transformation,[],[f9])).
% 1.33/0.54  fof(f9,negated_conjecture,(
% 1.33/0.54    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.33/0.54    inference(negated_conjecture,[],[f8])).
% 1.33/0.54  fof(f8,conjecture,(
% 1.33/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 1.33/0.54  fof(f46,plain,(
% 1.33/0.54    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) | ~r2_hidden(sK1,sK3) | sK0 != sK2 | ~spl4_2),
% 1.33/0.54    inference(backward_demodulation,[],[f23,f43])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.33/0.54    inference(cnf_transformation,[],[f17])).
% 1.33/0.54  fof(f55,plain,(
% 1.33/0.54    spl4_3 | ~spl4_2),
% 1.33/0.54    inference(avatar_split_clause,[],[f47,f41,f52])).
% 1.33/0.54  fof(f44,plain,(
% 1.33/0.54    spl4_1 | spl4_2),
% 1.33/0.54    inference(avatar_split_clause,[],[f21,f41,f37])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.33/0.54    inference(cnf_transformation,[],[f17])).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (6929)------------------------------
% 1.33/0.54  % (6929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (6929)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (6929)Memory used [KB]: 10874
% 1.33/0.54  % (6929)Time elapsed: 0.117 s
% 1.33/0.54  % (6929)------------------------------
% 1.33/0.54  % (6929)------------------------------
% 1.33/0.54  % (6916)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.55  % (6907)Success in time 0.18 s
%------------------------------------------------------------------------------
