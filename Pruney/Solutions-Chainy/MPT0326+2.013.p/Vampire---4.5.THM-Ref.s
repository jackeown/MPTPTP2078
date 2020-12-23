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
% DateTime   : Thu Dec  3 12:42:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  96 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 324 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f50,f74,f97,f104])).

fof(f104,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f16,f101])).

fof(f101,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl4_1
    | spl4_3 ),
    inference(resolution,[],[f93,f18])).

fof(f18,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f93,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X2))
        | r1_tarski(sK1,X2) )
    | ~ spl4_1
    | spl4_3 ),
    inference(global_subsumption,[],[f45,f85])).

fof(f85,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X2))
        | r1_tarski(sK1,X2)
        | k1_xboole_0 = sK0 )
    | ~ spl4_1 ),
    inference(superposition,[],[f20,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_1 ),
    inference(global_subsumption,[],[f16,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK1,sK3)
    | ~ spl4_1 ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f26,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl4_1
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f45,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f16,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK1,sK3)
    & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X3,X2,X1] :
        ( ~ r1_tarski(X1,X3)
        & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
          | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
   => ( ~ r1_tarski(sK1,sK3)
      & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
        | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f97,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f16,f95])).

fof(f95,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f49,f18])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0))
        | r1_tarski(sK1,X0) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_4
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0))
        | r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl4_3 ),
    inference(global_subsumption,[],[f17,f72])).

fof(f72,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f14,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f14,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f50,plain,
    ( spl4_3
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f35,f28,f48,f44])).

fof(f28,plain,
    ( spl4_2
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f35,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0))
        | r1_tarski(sK1,X0)
        | k1_xboole_0 = sK0 )
    | ~ spl4_2 ),
    inference(superposition,[],[f19,f33])).

fof(f33,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl4_2 ),
    inference(global_subsumption,[],[f16,f32])).

fof(f32,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | r1_tarski(sK1,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f21,f30])).

fof(f30,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f15,f28,f24])).

fof(f15,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (26280)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.41  % (26273)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.41  % (26274)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (26280)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f105,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f31,f50,f74,f97,f104])).
% 0.21/0.41  fof(f104,plain,(
% 0.21/0.41    ~spl4_1 | spl4_3),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.41  fof(f103,plain,(
% 0.21/0.41    $false | (~spl4_1 | spl4_3)),
% 0.21/0.41    inference(subsumption_resolution,[],[f16,f101])).
% 0.21/0.41  fof(f101,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(sK1,X0)) ) | (~spl4_1 | spl4_3)),
% 0.21/0.41    inference(resolution,[],[f93,f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.41  fof(f93,plain,(
% 0.21/0.41    ( ! [X2] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X2)) | r1_tarski(sK1,X2)) ) | (~spl4_1 | spl4_3)),
% 0.21/0.41    inference(global_subsumption,[],[f45,f85])).
% 0.21/0.41  fof(f85,plain,(
% 0.21/0.41    ( ! [X2] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X2)) | r1_tarski(sK1,X2) | k1_xboole_0 = sK0) ) | ~spl4_1),
% 0.21/0.41    inference(superposition,[],[f20,f81])).
% 0.21/0.41  fof(f81,plain,(
% 0.21/0.41    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_1),
% 0.21/0.41    inference(global_subsumption,[],[f16,f79])).
% 0.21/0.41  fof(f79,plain,(
% 0.21/0.41    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(sK1,sK3) | ~spl4_1),
% 0.21/0.41    inference(resolution,[],[f26,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X1,X3)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.41    inference(flattening,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f24])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    spl4_1 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    k1_xboole_0 != sK0 | spl4_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f44])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    spl4_3 <=> k1_xboole_0 = sK0),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ~r1_tarski(sK1,sK3)),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) & ~v1_xboole_0(sK0)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f12,f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0)) => (? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(sK0))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) => (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,negated_conjecture,(
% 0.21/0.41    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.21/0.41    inference(negated_conjecture,[],[f5])).
% 0.21/0.41  fof(f5,conjecture,(
% 0.21/0.41    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    ~spl4_4),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f96])).
% 0.21/0.41  fof(f96,plain,(
% 0.21/0.41    $false | ~spl4_4),
% 0.21/0.41    inference(subsumption_resolution,[],[f16,f95])).
% 0.21/0.41  fof(f95,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl4_4),
% 0.21/0.41    inference(resolution,[],[f49,f18])).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0)) | r1_tarski(sK1,X0)) ) | ~spl4_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f48])).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    spl4_4 <=> ! [X0] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0)) | r1_tarski(sK1,X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.41  fof(f74,plain,(
% 0.21/0.41    ~spl4_3),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f73])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    $false | ~spl4_3),
% 0.21/0.41    inference(global_subsumption,[],[f17,f72])).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    ~v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.21/0.41    inference(backward_demodulation,[],[f14,f46])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    k1_xboole_0 = sK0 | ~spl4_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f44])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ~v1_xboole_0(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    v1_xboole_0(k1_xboole_0)),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    v1_xboole_0(k1_xboole_0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    spl4_3 | spl4_4 | ~spl4_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f35,f28,f48,f44])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    spl4_2 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0)) | r1_tarski(sK1,X0) | k1_xboole_0 = sK0) ) | ~spl4_2),
% 0.21/0.41    inference(superposition,[],[f19,f33])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | ~spl4_2),
% 0.21/0.41    inference(global_subsumption,[],[f16,f32])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | r1_tarski(sK1,sK3) | ~spl4_2),
% 0.21/0.41    inference(resolution,[],[f21,f30])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | ~spl4_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f28])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X0,X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    spl4_1 | spl4_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f15,f28,f24])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (26280)------------------------------
% 0.21/0.41  % (26280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (26280)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (26280)Memory used [KB]: 10618
% 0.21/0.41  % (26280)Time elapsed: 0.007 s
% 0.21/0.41  % (26280)------------------------------
% 0.21/0.41  % (26280)------------------------------
% 0.21/0.42  % (26268)Success in time 0.061 s
%------------------------------------------------------------------------------
