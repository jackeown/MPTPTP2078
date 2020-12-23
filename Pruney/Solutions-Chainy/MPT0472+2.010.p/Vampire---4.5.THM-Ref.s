%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  68 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   99 ( 162 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f32,f39,f45,f48,f51])).

fof(f51,plain,
    ( spl1_6
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f50,f34,f30,f43])).

fof(f43,plain,
    ( spl1_6
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f30,plain,
    ( spl1_3
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f34,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f50,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f49,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f49,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(superposition,[],[f31,f35])).

fof(f35,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f31,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f48,plain,
    ( spl1_2
    | ~ spl1_6 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl1_2
    | ~ spl1_6 ),
    inference(subsumption_resolution,[],[f46,f27])).

fof(f27,plain,
    ( k1_xboole_0 != sK0
    | spl1_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl1_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f46,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_6 ),
    inference(resolution,[],[f44,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f44,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f45,plain,
    ( spl1_6
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f41,f37,f30,f43])).

fof(f37,plain,
    ( spl1_5
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f41,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f40,f19])).

fof(f19,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(superposition,[],[f31,f38])).

fof(f38,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f39,plain,
    ( spl1_4
    | spl1_5 ),
    inference(avatar_split_clause,[],[f10,f37,f34])).

fof(f10,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ( k1_xboole_0 = k2_relat_1(X0)
            | k1_xboole_0 = k1_relat_1(X0) )
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f32,plain,
    ( spl1_3
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f24,f21,f30])).

fof(f21,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f24,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_1 ),
    inference(resolution,[],[f22,f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f22,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f28,plain,(
    ~ spl1_2 ),
    inference(avatar_split_clause,[],[f12,f26])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f11,f21])).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:23:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (11038)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (11038)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f23,f28,f32,f39,f45,f48,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl1_6 | ~spl1_3 | ~spl1_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f50,f34,f30,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl1_6 <=> r1_tarski(sK0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    spl1_3 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl1_4 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    r1_tarski(sK0,k1_xboole_0) | (~spl1_3 | ~spl1_4)),
% 0.21/0.47    inference(forward_demodulation,[],[f49,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) | (~spl1_3 | ~spl1_4)),
% 0.21/0.47    inference(superposition,[],[f31,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f34])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f30])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl1_2 | ~spl1_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    $false | (spl1_2 | ~spl1_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f46,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    k1_xboole_0 != sK0 | spl1_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    spl1_2 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl1_6),
% 0.21/0.47    inference(resolution,[],[f44,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    r1_tarski(sK0,k1_xboole_0) | ~spl1_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl1_6 | ~spl1_3 | ~spl1_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f37,f30,f43])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl1_5 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    r1_tarski(sK0,k1_xboole_0) | (~spl1_3 | ~spl1_5)),
% 0.21/0.47    inference(forward_demodulation,[],[f40,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    r1_tarski(sK0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))) | (~spl1_3 | ~spl1_5)),
% 0.21/0.47    inference(superposition,[],[f31,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(sK0) | ~spl1_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f37])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl1_4 | spl1_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f10,f37,f34])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(sK0) | k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : ((k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl1_3 | ~spl1_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f21,f30])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    spl1_1 <=> v1_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_1),
% 0.21/0.47    inference(resolution,[],[f22,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    v1_relat_1(sK0) | ~spl1_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f21])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ~spl1_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f12,f26])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    k1_xboole_0 != sK0),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    spl1_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f11,f21])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (11038)------------------------------
% 0.21/0.47  % (11038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11038)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (11038)Memory used [KB]: 6140
% 0.21/0.47  % (11038)Time elapsed: 0.062 s
% 0.21/0.47  % (11038)------------------------------
% 0.21/0.47  % (11038)------------------------------
% 0.21/0.47  % (11049)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (11034)Success in time 0.112 s
%------------------------------------------------------------------------------
