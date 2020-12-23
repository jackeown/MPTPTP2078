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
% DateTime   : Thu Dec  3 12:44:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  70 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :  105 ( 173 expanded)
%              Number of equality atoms :   15 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f29,f35,f40,f45,f58,f65])).

fof(f65,plain,
    ( spl3_2
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f61,f28])).

fof(f28,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f61,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(resolution,[],[f57,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f57,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_7
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f58,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f54,f43,f23,f56])).

fof(f23,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,
    ( spl3_5
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f54,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f47,f30])).

fof(f30,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1))
    | ~ spl3_1 ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f24,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f47,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k4_xboole_0(sK0,sK2),X1)
        | r1_tarski(sK1,X1) )
    | ~ spl3_5 ),
    inference(resolution,[],[f44,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f44,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f45,plain,
    ( spl3_5
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f41,f38,f33,f43])).

fof(f33,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f38,plain,
    ( spl3_4
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f41,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f39,f36])).

fof(f36,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f34,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f39,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f40,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f17,f27])).

fof(f17,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f23])).

fof(f15,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:26:51 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.21/0.46  % (21195)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (21195)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (21203)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f25,f29,f35,f40,f45,f58,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl3_2 | ~spl3_7),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    $false | (spl3_2 | ~spl3_7)),
% 0.21/0.47    inference(subsumption_resolution,[],[f61,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    k1_xboole_0 != sK1 | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | ~spl3_7),
% 0.21/0.47    inference(resolution,[],[f57,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl3_7 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl3_7 | ~spl3_1 | ~spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f54,f43,f23,f56])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl3_5 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_5)),
% 0.21/0.47    inference(resolution,[],[f47,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1))) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f24,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f23])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X1] : (~r1_tarski(k4_xboole_0(sK0,sK2),X1) | r1_tarski(sK1,X1)) ) | ~spl3_5),
% 0.21/0.47    inference(resolution,[],[f44,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl3_5 | ~spl3_3 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f38,f33,f43])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    spl3_4 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | (~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(forward_demodulation,[],[f39,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f34,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f33])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f38])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f16,f38])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f14,f33])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f17,f27])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    k1_xboole_0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f15,f23])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    r1_tarski(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (21195)------------------------------
% 0.21/0.47  % (21195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21195)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (21195)Memory used [KB]: 6140
% 0.21/0.47  % (21195)Time elapsed: 0.053 s
% 0.21/0.47  % (21195)------------------------------
% 0.21/0.47  % (21195)------------------------------
% 0.21/0.48  % (21194)Success in time 0.117 s
%------------------------------------------------------------------------------
