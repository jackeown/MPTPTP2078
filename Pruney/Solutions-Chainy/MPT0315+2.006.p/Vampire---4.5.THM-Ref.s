%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  64 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 131 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f32,f54,f61,f75])).

fof(f75,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f31,f73])).

fof(f73,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK3))
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK3)) )
    | ~ spl4_5 ),
    inference(superposition,[],[f13,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK3))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f63,f15])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f63,plain,
    ( ! [X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK3))
    | ~ spl4_5 ),
    inference(superposition,[],[f9,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_5
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f9,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f31,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl4_4
  <=> r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f61,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f57,f18,f59])).

fof(f18,plain,
    ( spl4_1
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f57,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl4_1 ),
    inference(resolution,[],[f19,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f19,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f54,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f31,f52])).

fof(f52,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1)) )
    | ~ spl4_3 ),
    inference(superposition,[],[f13,f38])).

fof(f38,plain,
    ( ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f35,f16])).

fof(f16,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,
    ( ! [X2,X3] : k3_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X3))
    | ~ spl4_3 ),
    inference(superposition,[],[f9,f27])).

fof(f27,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl4_3
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f32,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f8,f30])).

fof(f8,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f28,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f24,f21,f26])).

fof(f21,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f24,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f22,f14])).

fof(f22,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f23,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f7,f21,f18])).

fof(f7,plain,
    ( r1_xboole_0(sK0,sK1)
    | r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (27243)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (27251)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (27242)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (27246)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (27242)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f23,f28,f32,f54,f61,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl4_4 | ~spl4_5),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    $false | (spl4_4 | ~spl4_5)),
% 0.20/0.47    inference(subsumption_resolution,[],[f31,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK3))) ) | ~spl4_5),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK3))) ) | ~spl4_5),
% 0.20/0.47    inference(superposition,[],[f13,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK3))) ) | ~spl4_5),
% 0.20/0.47    inference(forward_demodulation,[],[f63,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK3))) ) | ~spl4_5),
% 0.20/0.47    inference(superposition,[],[f9,f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl4_5 <=> k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) | spl4_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    spl4_4 <=> r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl4_5 | ~spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f57,f18,f59])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    spl4_1 <=> r1_xboole_0(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f19,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    r1_xboole_0(sK2,sK3) | ~spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f18])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ~spl4_3 | spl4_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    $false | (~spl4_3 | spl4_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f31,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) ) | ~spl4_3),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) ) | ~spl4_3),
% 0.20/0.47    inference(superposition,[],[f13,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3))) ) | ~spl4_3),
% 0.20/0.47    inference(forward_demodulation,[],[f35,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k3_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X3))) ) | ~spl4_3),
% 0.20/0.47    inference(superposition,[],[f9,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    spl4_3 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ~spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f8,f30])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.47    inference(negated_conjecture,[],[f4])).
% 0.20/0.47  fof(f4,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    spl4_3 | ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f24,f21,f26])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    spl4_2 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_2),
% 0.20/0.47    inference(resolution,[],[f22,f14])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK1) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f21])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    spl4_1 | spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f7,f21,f18])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK1) | r1_xboole_0(sK2,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (27242)------------------------------
% 0.20/0.47  % (27242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (27242)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (27242)Memory used [KB]: 6140
% 0.20/0.47  % (27242)Time elapsed: 0.062 s
% 0.20/0.47  % (27242)------------------------------
% 0.20/0.47  % (27242)------------------------------
% 0.20/0.47  % (27255)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (27243)Refutation not found, incomplete strategy% (27243)------------------------------
% 0.20/0.47  % (27243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (27243)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (27243)Memory used [KB]: 10490
% 0.20/0.47  % (27243)Time elapsed: 0.066 s
% 0.20/0.47  % (27243)------------------------------
% 0.20/0.47  % (27243)------------------------------
% 0.20/0.48  % (27238)Success in time 0.118 s
%------------------------------------------------------------------------------
