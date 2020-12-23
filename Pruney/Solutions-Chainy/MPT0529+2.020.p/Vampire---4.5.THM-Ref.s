%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  76 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :  133 ( 194 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f55,f76,f114,f172,f181])).

fof(f181,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f177,f27])).

fof(f27,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f177,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_27 ),
    inference(resolution,[],[f171,f32])).

fof(f32,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_27
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f172,plain,
    ( spl3_27
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f168,f112,f35,f170])).

fof(f35,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f112,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X1,X2)
        | k8_relat_1(X0,sK2) = k8_relat_1(X2,k8_relat_1(X0,sK2))
        | ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f166,f37])).

fof(f37,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_17 ),
    inference(resolution,[],[f113,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f113,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X2,k8_relat_1(X0,sK2))
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f112])).

fof(f114,plain,
    ( spl3_17
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f106,f74,f112])).

fof(f74,plain,
    ( spl3_10
  <=> ! [X1,X3,X2] :
        ( k8_relat_1(X1,sK2) = k8_relat_1(X2,k8_relat_1(X1,sK2))
        | ~ r1_tarski(k2_xboole_0(k2_relat_1(k8_relat_1(X1,sK2)),X3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | k8_relat_1(X0,sK2) = k8_relat_1(X2,k8_relat_1(X0,sK2))
        | ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1) )
    | ~ spl3_10 ),
    inference(superposition,[],[f75,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f75,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(k2_xboole_0(k2_relat_1(k8_relat_1(X1,sK2)),X3),X2)
        | k8_relat_1(X1,sK2) = k8_relat_1(X2,k8_relat_1(X1,sK2)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,
    ( spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f67,f53,f74])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f67,plain,
    ( ! [X2,X3,X1] :
        ( k8_relat_1(X1,sK2) = k8_relat_1(X2,k8_relat_1(X1,sK2))
        | ~ r1_tarski(k2_xboole_0(k2_relat_1(k8_relat_1(X1,sK2)),X3),X2) )
    | ~ spl3_6 ),
    inference(resolution,[],[f54,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f55,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f50,f35,f53])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1) )
    | ~ spl3_3 ),
    inference(resolution,[],[f40,f37])).

fof(f40,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X1,X2) = k8_relat_1(X3,k8_relat_1(X1,X2))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X3) ) ),
    inference(resolution,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f25])).

fof(f18,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:17:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (21456)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.42  % (21462)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (21457)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (21457)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f190,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f28,f33,f38,f55,f76,f114,f172,f181])).
% 0.21/0.43  fof(f181,plain,(
% 0.21/0.43    spl3_1 | ~spl3_2 | ~spl3_27),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f180])).
% 0.21/0.43  fof(f180,plain,(
% 0.21/0.43    $false | (spl3_1 | ~spl3_2 | ~spl3_27)),
% 0.21/0.43    inference(subsumption_resolution,[],[f177,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    spl3_1 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f177,plain,(
% 0.21/0.43    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | (~spl3_2 | ~spl3_27)),
% 0.21/0.43    inference(resolution,[],[f171,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f171,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))) ) | ~spl3_27),
% 0.21/0.43    inference(avatar_component_clause,[],[f170])).
% 0.21/0.43  fof(f170,plain,(
% 0.21/0.43    spl3_27 <=> ! [X1,X0] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    spl3_27 | ~spl3_3 | ~spl3_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f168,f112,f35,f170])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    spl3_17 <=> ! [X1,X0,X2] : (~r1_tarski(X1,X2) | k8_relat_1(X0,sK2) = k8_relat_1(X2,k8_relat_1(X0,sK2)) | ~r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.43  fof(f168,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(X0,X1)) ) | (~spl3_3 | ~spl3_17)),
% 0.21/0.43    inference(subsumption_resolution,[],[f166,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f35])).
% 0.21/0.43  fof(f166,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(sK2)) ) | ~spl3_17),
% 0.21/0.43    inference(resolution,[],[f113,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1) | k8_relat_1(X0,sK2) = k8_relat_1(X2,k8_relat_1(X0,sK2)) | ~r1_tarski(X1,X2)) ) | ~spl3_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f112])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    spl3_17 | ~spl3_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f106,f74,f112])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    spl3_10 <=> ! [X1,X3,X2] : (k8_relat_1(X1,sK2) = k8_relat_1(X2,k8_relat_1(X1,sK2)) | ~r1_tarski(k2_xboole_0(k2_relat_1(k8_relat_1(X1,sK2)),X3),X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | k8_relat_1(X0,sK2) = k8_relat_1(X2,k8_relat_1(X0,sK2)) | ~r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1)) ) | ~spl3_10),
% 0.21/0.43    inference(superposition,[],[f75,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ( ! [X2,X3,X1] : (~r1_tarski(k2_xboole_0(k2_relat_1(k8_relat_1(X1,sK2)),X3),X2) | k8_relat_1(X1,sK2) = k8_relat_1(X2,k8_relat_1(X1,sK2))) ) | ~spl3_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f74])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    spl3_10 | ~spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f67,f53,f74])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl3_6 <=> ! [X1,X0] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    ( ! [X2,X3,X1] : (k8_relat_1(X1,sK2) = k8_relat_1(X2,k8_relat_1(X1,sK2)) | ~r1_tarski(k2_xboole_0(k2_relat_1(k8_relat_1(X1,sK2)),X3),X2)) ) | ~spl3_6),
% 0.21/0.43    inference(resolution,[],[f54,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))) ) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f53])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl3_6 | ~spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f50,f35,f53])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1)) ) | ~spl3_3),
% 0.21/0.43    inference(resolution,[],[f40,f37])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X2,X3,X1] : (~v1_relat_1(X2) | k8_relat_1(X1,X2) = k8_relat_1(X3,k8_relat_1(X1,X2)) | ~r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X3)) )),
% 0.21/0.43    inference(resolution,[],[f21,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f35])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    v1_relat_1(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f30])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f25])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (21457)------------------------------
% 0.21/0.43  % (21457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (21457)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (21457)Memory used [KB]: 10618
% 0.21/0.43  % (21457)Time elapsed: 0.009 s
% 0.21/0.43  % (21457)------------------------------
% 0.21/0.43  % (21457)------------------------------
% 0.21/0.43  % (21468)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.44  % (21453)Success in time 0.071 s
%------------------------------------------------------------------------------
