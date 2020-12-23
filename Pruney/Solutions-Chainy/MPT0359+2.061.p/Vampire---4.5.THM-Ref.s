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
% DateTime   : Thu Dec  3 12:44:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 124 expanded)
%              Number of leaves         :   13 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 269 expanded)
%              Number of equality atoms :   34 (  74 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f80,f134,f191,f216])).

fof(f216,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f196,f94])).

fof(f94,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f93,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f93,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f34,f91,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f91,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f75,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f75,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f34,f64,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f53,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f196,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f59,f56])).

fof(f56,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f46,f38])).

fof(f46,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f19,f33])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f191,plain,
    ( spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl3_2
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f151,f57])).

fof(f57,plain,
    ( sK0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f151,plain,
    ( sK0 = sK1
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f136,f37])).

fof(f37,plain,(
    ! [X0] : k3_subset_1(X0,k1_subset_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f21,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f22,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f136,plain,
    ( sK1 = k3_subset_1(sK0,k1_subset_1(sK0))
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f45,f133])).

fof(f133,plain,
    ( k3_subset_1(sK0,sK1) = k1_subset_1(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_6
  <=> k3_subset_1(sK0,sK1) = k1_subset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f45,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f134,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f73,f77,f131])).

fof(f77,plain,
    ( spl3_3
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f73,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) = k1_subset_1(sK0) ),
    inference(forward_demodulation,[],[f69,f45])).

fof(f69,plain,
    ( k3_subset_1(sK0,sK1) = k1_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f44,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f19,f29])).

fof(f80,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f43,f55,f77])).

fof(f43,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f36,f37])).

fof(f36,plain,
    ( sK1 = k3_subset_1(sK0,k1_subset_1(sK0))
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f17,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f55,f51])).

fof(f42,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(inner_rewriting,[],[f41])).

fof(f41,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f35,f37])).

fof(f35,plain,
    ( sK1 != k3_subset_1(sK0,k1_subset_1(sK0))
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f18,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (19772)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.49  % (19764)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (19771)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (19753)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (19775)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.50  % (19753)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f58,f80,f134,f191,f216])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    spl3_1 | ~spl3_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f212])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    $false | (spl3_1 | ~spl3_2)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f196,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ~r1_tarski(sK0,sK0) | spl3_1),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f93,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(equality_resolution,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | spl3_1),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f34,f91,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_1),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f75,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ~m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | spl3_1),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f34,f64,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ~r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | spl3_1),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f53,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    r1_tarski(sK0,sK0) | ~spl3_2),
% 0.20/0.50    inference(backward_demodulation,[],[f59,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    sK0 = sK1 | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    spl3_2 <=> sK0 = sK1),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    r1_tarski(sK1,sK0)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f46,f38])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f34,f19,f33])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    spl3_2 | ~spl3_6),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f187])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    $false | (spl3_2 | ~spl3_6)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f151,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    sK0 != sK1 | spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f55])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    sK0 = sK1 | ~spl3_6),
% 0.20/0.50    inference(forward_demodulation,[],[f136,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (k3_subset_1(X0,k1_subset_1(X0)) = X0) )),
% 0.20/0.50    inference(definition_unfolding,[],[f22,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    sK1 = k3_subset_1(sK0,k1_subset_1(sK0)) | ~spl3_6),
% 0.20/0.50    inference(backward_demodulation,[],[f45,f133])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    k3_subset_1(sK0,sK1) = k1_subset_1(sK0) | ~spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f131])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    spl3_6 <=> k3_subset_1(sK0,sK1) = k1_subset_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f19,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    spl3_6 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f73,f77,f131])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl3_3 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | k3_subset_1(sK0,sK1) = k1_subset_1(sK0)),
% 0.20/0.50    inference(forward_demodulation,[],[f69,f45])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    k3_subset_1(sK0,sK1) = k1_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK1)))),
% 0.20/0.50    inference(resolution,[],[f44,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f19,f29])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl3_3 | spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f43,f55,f77])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.50    inference(forward_demodulation,[],[f36,f37])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    sK1 = k3_subset_1(sK0,k1_subset_1(sK0)) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.50    inference(definition_unfolding,[],[f17,f21])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ~spl3_1 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f42,f55,f51])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.20/0.50    inference(inner_rewriting,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.50    inference(forward_demodulation,[],[f35,f37])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    sK1 != k3_subset_1(sK0,k1_subset_1(sK0)) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.50    inference(definition_unfolding,[],[f18,f21])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (19753)------------------------------
% 0.20/0.50  % (19753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (19753)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (19753)Memory used [KB]: 6268
% 0.20/0.50  % (19753)Time elapsed: 0.097 s
% 0.20/0.50  % (19753)------------------------------
% 0.20/0.50  % (19753)------------------------------
% 0.20/0.50  % (19756)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (19748)Success in time 0.15 s
%------------------------------------------------------------------------------
