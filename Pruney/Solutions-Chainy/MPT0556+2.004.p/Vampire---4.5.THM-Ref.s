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
% DateTime   : Thu Dec  3 12:49:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  93 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  139 ( 337 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1651,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f73,f77,f81,f94,f1644,f1650])).

fof(f1650,plain,
    ( ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | spl6_35 ),
    inference(avatar_split_clause,[],[f1645,f1642,f71,f75,f79])).

fof(f79,plain,
    ( spl6_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f75,plain,
    ( spl6_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f71,plain,
    ( spl6_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1642,plain,
    ( spl6_35
  <=> r1_tarski(k9_relat_1(sK2,sK1),k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f1645,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl6_35 ),
    inference(resolution,[],[f1643,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f1643,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK1),k9_relat_1(sK3,sK1))
    | spl6_35 ),
    inference(avatar_component_clause,[],[f1642])).

fof(f1644,plain,
    ( ~ spl6_35
    | spl6_1
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f1636,f92,f79,f63,f1642])).

fof(f63,plain,
    ( spl6_1
  <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f92,plain,
    ( spl6_6
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1636,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK1),k9_relat_1(sK3,sK1))
    | spl6_1
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(superposition,[],[f1254,f93])).

fof(f93,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f1254,plain,
    ( ! [X0] : ~ r1_tarski(k9_relat_1(sK2,k2_xboole_0(sK0,X0)),k9_relat_1(sK3,sK1))
    | spl6_1
    | ~ spl6_5 ),
    inference(superposition,[],[f107,f806])).

% (18191)Refutation not found, incomplete strategy% (18191)------------------------------
% (18191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18191)Termination reason: Refutation not found, incomplete strategy

% (18191)Memory used [KB]: 10746
% (18191)Time elapsed: 0.105 s
% (18191)------------------------------
% (18191)------------------------------
fof(f806,plain,
    ( ! [X2,X3] : k9_relat_1(sK2,k2_xboole_0(X2,X3)) = k2_xboole_0(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3))
    | ~ spl6_5 ),
    inference(resolution,[],[f49,f80])).

fof(f80,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(f107,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k9_relat_1(sK2,sK0),X0),k9_relat_1(sK3,sK1))
    | spl6_1 ),
    inference(resolution,[],[f50,f64])).

fof(f64,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f94,plain,
    ( spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f86,f67,f92])).

fof(f67,plain,
    ( spl6_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f86,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f42,f68])).

fof(f68,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f81,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f34,f79])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

fof(f77,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f36,f71])).

fof(f36,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f37,f67])).

fof(f37,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f38,f63])).

fof(f38,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.51  % (18188)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (18175)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (18191)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (18188)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f1651,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f65,f69,f73,f77,f81,f94,f1644,f1650])).
% 0.22/0.54  fof(f1650,plain,(
% 0.22/0.54    ~spl6_5 | ~spl6_4 | ~spl6_3 | spl6_35),
% 0.22/0.54    inference(avatar_split_clause,[],[f1645,f1642,f71,f75,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    spl6_5 <=> v1_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    spl6_4 <=> v1_relat_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    spl6_3 <=> r1_tarski(sK2,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.54  fof(f1642,plain,(
% 0.22/0.54    spl6_35 <=> r1_tarski(k9_relat_1(sK2,sK1),k9_relat_1(sK3,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.22/0.54  fof(f1645,plain,(
% 0.22/0.54    ~r1_tarski(sK2,sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | spl6_35),
% 0.22/0.54    inference(resolution,[],[f1643,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 0.22/0.54  fof(f1643,plain,(
% 0.22/0.54    ~r1_tarski(k9_relat_1(sK2,sK1),k9_relat_1(sK3,sK1)) | spl6_35),
% 0.22/0.54    inference(avatar_component_clause,[],[f1642])).
% 0.22/0.54  fof(f1644,plain,(
% 0.22/0.54    ~spl6_35 | spl6_1 | ~spl6_5 | ~spl6_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f1636,f92,f79,f63,f1642])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    spl6_1 <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    spl6_6 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.54  fof(f1636,plain,(
% 0.22/0.54    ~r1_tarski(k9_relat_1(sK2,sK1),k9_relat_1(sK3,sK1)) | (spl6_1 | ~spl6_5 | ~spl6_6)),
% 0.22/0.54    inference(superposition,[],[f1254,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    sK1 = k2_xboole_0(sK0,sK1) | ~spl6_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f92])).
% 0.22/0.54  fof(f1254,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,k2_xboole_0(sK0,X0)),k9_relat_1(sK3,sK1))) ) | (spl6_1 | ~spl6_5)),
% 0.22/0.54    inference(superposition,[],[f107,f806])).
% 0.22/0.54  % (18191)Refutation not found, incomplete strategy% (18191)------------------------------
% 0.22/0.54  % (18191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18191)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18191)Memory used [KB]: 10746
% 0.22/0.54  % (18191)Time elapsed: 0.105 s
% 0.22/0.54  % (18191)------------------------------
% 0.22/0.54  % (18191)------------------------------
% 0.22/0.54  fof(f806,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k9_relat_1(sK2,k2_xboole_0(X2,X3)) = k2_xboole_0(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3))) ) | ~spl6_5),
% 0.22/0.54    inference(resolution,[],[f49,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    v1_relat_1(sK2) | ~spl6_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f79])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k2_xboole_0(k9_relat_1(sK2,sK0),X0),k9_relat_1(sK3,sK1))) ) | spl6_1),
% 0.22/0.54    inference(resolution,[],[f50,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) | spl6_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f63])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    spl6_6 | ~spl6_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f86,f67,f92])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    spl6_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    sK1 = k2_xboole_0(sK0,sK1) | ~spl6_2),
% 0.22/0.54    inference(resolution,[],[f42,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1) | ~spl6_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f67])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    spl6_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f34,f79])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    v1_relat_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ? [X3] : (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f10])).
% 0.22/0.54  fof(f10,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    spl6_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f35,f75])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    v1_relat_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    spl6_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f36,f71])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    r1_tarski(sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    spl6_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f37,f67])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ~spl6_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f38,f63])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (18188)------------------------------
% 0.22/0.54  % (18188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18188)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (18188)Memory used [KB]: 11897
% 0.22/0.54  % (18188)Time elapsed: 0.126 s
% 0.22/0.54  % (18188)------------------------------
% 0.22/0.54  % (18188)------------------------------
% 0.22/0.54  % (18168)Success in time 0.174 s
%------------------------------------------------------------------------------
