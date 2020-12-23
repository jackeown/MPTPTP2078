%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 170 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  153 ( 373 expanded)
%              Number of equality atoms :   42 ( 108 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f99,f161,f221,f256])).

fof(f256,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f227,f113])).

fof(f113,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f112,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f112,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f39,f110,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f110,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f94,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f94,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f39,f77,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f66,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f227,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f72,f69])).

fof(f69,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f72,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f52,f43])).

fof(f52,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f22,f36])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f221,plain,
    ( spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl3_2
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f70,f180])).

fof(f180,plain,
    ( sK0 = sK1
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f166,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f166,plain,
    ( sK1 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f88,f160])).

fof(f160,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f88,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f78,f58])).

fof(f58,plain,(
    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f51,f49])).

fof(f49,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f22,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f51,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f78,plain,(
    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f40])).

fof(f57,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f50,f49])).

fof(f50,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f22,f32])).

fof(f70,plain,
    ( sK0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f161,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f91,f96,f158])).

fof(f96,plain,
    ( spl3_3
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f91,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f84,f58])).

fof(f84,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f57,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f99,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f59,f96,f68])).

fof(f59,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f48,f49])).

fof(f48,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f20,f24])).

fof(f24,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f20,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f47,f68,f64])).

fof(f47,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(inner_rewriting,[],[f46])).

fof(f46,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f21,f24])).

fof(f21,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:34:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (22326)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (22347)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (22349)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (22327)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (22325)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (22328)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (22330)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (22329)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (22341)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (22329)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f257,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f71,f99,f161,f221,f256])).
% 0.20/0.52  fof(f256,plain,(
% 0.20/0.52    spl3_1 | ~spl3_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f252])).
% 0.20/0.52  fof(f252,plain,(
% 0.20/0.52    $false | (spl3_1 | ~spl3_2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f227,f113])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    ~r1_tarski(sK0,sK0) | spl3_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f112,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(equality_resolution,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | spl3_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f39,f110,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f94,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ~m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | spl3_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f39,f77,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ~r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | spl3_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f66,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl3_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    r1_tarski(sK0,sK0) | ~spl3_2),
% 0.20/0.52    inference(backward_demodulation,[],[f72,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    sK0 = sK1 | ~spl3_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    spl3_2 <=> sK0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    r1_tarski(sK1,sK0)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f52,f43])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f39,f22,f36])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.20/0.52    inference(negated_conjecture,[],[f12])).
% 0.20/0.52  fof(f12,conjecture,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.20/0.52  fof(f221,plain,(
% 0.20/0.52    spl3_2 | ~spl3_6),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f217])).
% 0.20/0.52  fof(f217,plain,(
% 0.20/0.52    $false | (spl3_2 | ~spl3_6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f70,f180])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    sK0 = sK1 | ~spl3_6),
% 0.20/0.52    inference(forward_demodulation,[],[f166,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    sK1 = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_6),
% 0.20/0.52    inference(backward_demodulation,[],[f88,f160])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f158])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.52    inference(forward_demodulation,[],[f78,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.52    inference(backward_demodulation,[],[f51,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f22,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f22,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f57,f40])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(backward_demodulation,[],[f50,f49])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f22,f32])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    sK0 != sK1 | spl3_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f68])).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    spl3_6 | ~spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f91,f96,f158])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    spl3_3 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ~r1_tarski(k4_xboole_0(sK0,sK1),sK1) | k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f84,f58])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.52    inference(resolution,[],[f57,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f30,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    spl3_2 | spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f59,f96,f68])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | sK0 = sK1),
% 0.20/0.52    inference(backward_demodulation,[],[f48,f49])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f20,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ~spl3_1 | ~spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f47,f68,f64])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.20/0.52    inference(inner_rewriting,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f21,f24])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (22329)------------------------------
% 0.20/0.52  % (22329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22329)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (22329)Memory used [KB]: 6268
% 0.20/0.52  % (22329)Time elapsed: 0.109 s
% 0.20/0.52  % (22329)------------------------------
% 0.20/0.52  % (22329)------------------------------
% 0.20/0.52  % (22336)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (22334)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (22340)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (22339)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (22343)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (22334)Refutation not found, incomplete strategy% (22334)------------------------------
% 0.20/0.52  % (22334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22334)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (22334)Memory used [KB]: 10618
% 0.20/0.52  % (22334)Time elapsed: 0.117 s
% 0.20/0.52  % (22334)------------------------------
% 0.20/0.52  % (22334)------------------------------
% 0.20/0.52  % (22321)Success in time 0.161 s
%------------------------------------------------------------------------------
