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
% DateTime   : Thu Dec  3 12:48:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  77 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 195 expanded)
%              Number of equality atoms :   40 (  71 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f45,f52,f58,f62])).

fof(f62,plain,
    ( ~ spl1_1
    | ~ spl1_3
    | spl1_5 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_3
    | spl1_5 ),
    inference(subsumption_resolution,[],[f60,f50])).

fof(f50,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl1_5
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f60,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f59,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f59,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f36,f40])).

fof(f40,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl1_3
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f36,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_1 ),
    inference(resolution,[],[f29,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f29,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f58,plain,
    ( spl1_2
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl1_2
    | ~ spl1_5 ),
    inference(resolution,[],[f56,f51])).

fof(f51,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f56,plain,
    ( ! [X0] : ~ r1_tarski(sK0,X0)
    | spl1_2
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f55,f16])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f55,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0) )
    | spl1_2
    | ~ spl1_5 ),
    inference(resolution,[],[f54,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f54,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | ~ r1_tarski(sK0,X0) )
    | spl1_2
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f53,f34])).

fof(f34,plain,
    ( k1_xboole_0 != sK0
    | spl1_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl1_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = sK0 )
    | ~ spl1_5 ),
    inference(resolution,[],[f51,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f52,plain,
    ( spl1_5
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f47,f42,f27,f49])).

fof(f42,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f47,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f46,f25])).

fof(f25,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f36,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f45,plain,
    ( spl1_3
    | spl1_4 ),
    inference(avatar_split_clause,[],[f13,f42,f38])).

fof(f13,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ( k1_xboole_0 = k2_relat_1(X0)
            | k1_xboole_0 = k1_relat_1(X0) )
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f35,plain,(
    ~ spl1_2 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:56:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (12222)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.43  % (12222)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f30,f35,f45,f52,f58,f62])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ~spl1_1 | ~spl1_3 | spl1_5),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f61])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    $false | (~spl1_1 | ~spl1_3 | spl1_5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f60,f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ~r1_tarski(sK0,k1_xboole_0) | spl1_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl1_5 <=> r1_tarski(sK0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    r1_tarski(sK0,k1_xboole_0) | (~spl1_1 | ~spl1_3)),
% 0.21/0.43    inference(forward_demodulation,[],[f59,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(equality_resolution,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) | (~spl1_1 | ~spl1_3)),
% 0.21/0.43    inference(forward_demodulation,[],[f36,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl1_3 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_1),
% 0.21/0.43    inference(resolution,[],[f29,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    v1_relat_1(sK0) | ~spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    spl1_1 <=> v1_relat_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl1_2 | ~spl1_5),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    $false | (spl1_2 | ~spl1_5)),
% 0.21/0.43    inference(resolution,[],[f56,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    r1_tarski(sK0,k1_xboole_0) | ~spl1_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f49])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(sK0,X0)) ) | (spl1_2 | ~spl1_5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f55,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(sK0,X0) | k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)) ) | (spl1_2 | ~spl1_5)),
% 0.21/0.43    inference(resolution,[],[f54,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | ~r1_tarski(sK0,X0)) ) | (spl1_2 | ~spl1_5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f53,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    k1_xboole_0 != sK0 | spl1_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl1_2 <=> k1_xboole_0 = sK0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = sK0) ) | ~spl1_5),
% 0.21/0.43    inference(resolution,[],[f51,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl1_5 | ~spl1_1 | ~spl1_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f47,f42,f27,f49])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    spl1_4 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    r1_tarski(sK0,k1_xboole_0) | (~spl1_1 | ~spl1_4)),
% 0.21/0.43    inference(forward_demodulation,[],[f46,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.43    inference(equality_resolution,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    r1_tarski(sK0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))) | (~spl1_1 | ~spl1_4)),
% 0.21/0.43    inference(forward_demodulation,[],[f36,f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(sK0) | ~spl1_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f42])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl1_3 | spl1_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f13,f42,f38])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(sK0) | k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0] : ((k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ~spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f15,f32])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    k1_xboole_0 != sK0),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    spl1_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f14,f27])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (12222)------------------------------
% 0.21/0.43  % (12222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (12222)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (12222)Memory used [KB]: 10618
% 0.21/0.43  % (12222)Time elapsed: 0.006 s
% 0.21/0.43  % (12222)------------------------------
% 0.21/0.43  % (12222)------------------------------
% 0.21/0.44  % (12218)Success in time 0.076 s
%------------------------------------------------------------------------------
