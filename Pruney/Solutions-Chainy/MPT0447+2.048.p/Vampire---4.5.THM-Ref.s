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
% DateTime   : Thu Dec  3 12:47:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 172 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   17
%              Number of atoms          :  199 ( 632 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f78,f119,f123])).

fof(f123,plain,
    ( spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f120,f67])).

fof(f67,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_4
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f120,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | spl3_2 ),
    inference(resolution,[],[f59,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_relat_1(sK1))
      | ~ r1_tarski(X0,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f36,f42])).

fof(f42,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f29,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f59,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_2
  <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f119,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f117,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f117,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f116,f26])).

fof(f116,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f114,f27])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f114,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(resolution,[],[f113,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f113,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | spl3_1 ),
    inference(resolution,[],[f84,f46])).

fof(f46,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f32,f42])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f84,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k3_relat_1(sK1))
        | ~ r1_tarski(k1_relat_1(sK0),X2) )
    | spl3_1 ),
    inference(resolution,[],[f81,f55])).

fof(f55,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_1
  <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f72,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK2(X4,X3),X5)
      | r1_tarski(X4,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X5,X2) ) ),
    inference(resolution,[],[f40,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X2)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f33,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f76,f25])).

fof(f76,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_4 ),
    inference(subsumption_resolution,[],[f75,f26])).

fof(f75,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_4 ),
    inference(subsumption_resolution,[],[f74,f27])).

fof(f74,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_4 ),
    inference(resolution,[],[f31,f68])).

fof(f68,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f50,f57,f53])).

fof(f50,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f48,f28])).

fof(f28,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f37,f41])).

fof(f41,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f29,f25])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:26:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (1545)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (1545)Refutation not found, incomplete strategy% (1545)------------------------------
% 0.21/0.49  % (1545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1553)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  % (1545)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (1545)Memory used [KB]: 10746
% 0.21/0.49  % (1545)Time elapsed: 0.071 s
% 0.21/0.49  % (1545)------------------------------
% 0.21/0.49  % (1545)------------------------------
% 0.21/0.50  % (1540)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (1540)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (1555)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (1561)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (1547)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (1547)Refutation not found, incomplete strategy% (1547)------------------------------
% 0.21/0.51  % (1547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1547)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1547)Memory used [KB]: 10618
% 0.21/0.51  % (1547)Time elapsed: 0.098 s
% 0.21/0.51  % (1547)------------------------------
% 0.21/0.51  % (1547)------------------------------
% 0.21/0.52  % (1549)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (1548)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f60,f78,f119,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    spl3_2 | ~spl3_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    $false | (spl3_2 | ~spl3_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f120,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl3_4 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | spl3_2),
% 0.21/0.52    inference(resolution,[],[f59,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,k3_relat_1(sK1)) | ~r1_tarski(X0,k2_relat_1(sK1))) )),
% 0.21/0.52    inference(superposition,[],[f36,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.21/0.52    inference(resolution,[],[f29,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl3_2 <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    spl3_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    $false | spl3_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    v1_relat_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ~v1_relat_1(sK0) | spl3_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f116,f26])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f114,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    r1_tarski(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_1),
% 0.21/0.52    inference(resolution,[],[f113,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | spl3_1),
% 0.21/0.52    inference(resolution,[],[f84,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 0.21/0.52    inference(superposition,[],[f32,f42])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X2] : (~r1_tarski(X2,k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),X2)) ) | spl3_1),
% 0.21/0.52    inference(resolution,[],[f81,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl3_1 <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X2)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f72,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK2(X4,X3),X5) | r1_tarski(X4,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X5,X2)) )),
% 0.21/0.52    inference(resolution,[],[f40,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1),X2) | ~r1_tarski(X2,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f33,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl3_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    $false | spl3_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f76,f25])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ~v1_relat_1(sK0) | spl3_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f75,f26])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f74,f27])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_4),
% 0.21/0.52    inference(resolution,[],[f31,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f50,f57,f53])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.52    inference(resolution,[],[f48,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 0.21/0.52    inference(superposition,[],[f37,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.52    inference(resolution,[],[f29,f25])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (1540)------------------------------
% 0.21/0.52  % (1540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1540)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (1540)Memory used [KB]: 10746
% 0.21/0.52  % (1540)Time elapsed: 0.098 s
% 0.21/0.52  % (1540)------------------------------
% 0.21/0.52  % (1540)------------------------------
% 0.21/0.52  % (1554)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (1536)Success in time 0.162 s
%------------------------------------------------------------------------------
