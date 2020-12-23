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
% DateTime   : Thu Dec  3 12:29:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 104 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 310 expanded)
%              Number of equality atoms :   31 (  73 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1501,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f28,f32,f45,f66,f117,f124,f260,f1500])).

fof(f1500,plain,
    ( spl3_1
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f1498,f249,f22])).

fof(f22,plain,
    ( spl3_1
  <=> sK1 = k2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f249,plain,
    ( spl3_17
  <=> sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1498,plain,
    ( sK1 = k2_xboole_0(sK0,sK2)
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f1497,f250])).

fof(f250,plain,
    ( sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f249])).

fof(f1497,plain,(
    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1492,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1492,plain,(
    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f181,f33])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f17,f18])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f181,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,k2_xboole_0(sK2,X0))
      | k2_xboole_0(sK2,X0) = k2_xboole_0(sK1,k2_xboole_0(sK2,X0)) ) ),
    inference(resolution,[],[f39,f17])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | k2_xboole_0(sK1,X0) = X0
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f19,f15])).

fof(f15,plain,(
    ! [X3] :
      ( r1_tarski(sK1,X3)
      | ~ r1_tarski(sK2,X3)
      | ~ r1_tarski(sK0,X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK1 != k2_xboole_0(sK0,sK2)
    & ! [X3] :
        ( r1_tarski(sK1,X3)
        | ~ r1_tarski(sK2,X3)
        | ~ r1_tarski(sK0,X3) )
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(X0,X2) != X1
        & ! [X3] :
            ( r1_tarski(X1,X3)
            | ~ r1_tarski(X2,X3)
            | ~ r1_tarski(X0,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( sK1 != k2_xboole_0(sK0,sK2)
      & ! [X3] :
          ( r1_tarski(sK1,X3)
          | ~ r1_tarski(sK2,X3)
          | ~ r1_tarski(sK0,X3) )
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) != X1
      & ! [X3] :
          ( r1_tarski(X1,X3)
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X3) )
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) != X1
      & ! [X3] :
          ( r1_tarski(X1,X3)
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X3) )
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( ( r1_tarski(X2,X3)
                & r1_tarski(X0,X3) )
             => r1_tarski(X1,X3) )
          & r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => k2_xboole_0(X0,X2) = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f260,plain,
    ( spl3_17
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f246,f122,f249])).

fof(f122,plain,
    ( spl3_12
  <=> sK1 = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f246,plain,
    ( sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl3_12 ),
    inference(superposition,[],[f18,f123])).

fof(f123,plain,
    ( sK1 = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f124,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f120,f115,f122])).

fof(f115,plain,
    ( spl3_11
  <=> r1_tarski(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f120,plain,
    ( sK1 = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl3_11 ),
    inference(resolution,[],[f116,f19])).

fof(f116,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f110,f57,f30,f115])).

fof(f30,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f57,plain,
    ( spl3_6
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f110,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(superposition,[],[f77,f58])).

fof(f58,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f77,plain,
    ( ! [X1] : r1_tarski(k2_xboole_0(sK0,X1),k2_xboole_0(sK1,X1))
    | ~ spl3_3 ),
    inference(resolution,[],[f20,f31])).

fof(f31,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f66,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f54,f43,f57])).

fof(f43,plain,
    ( spl3_4
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f54,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f18,f44])).

fof(f44,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f45,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f37,f26,f43])).

fof(f26,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f37,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f19,f27])).

fof(f27,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f32,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f30])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f16,f22])).

fof(f16,plain,(
    sK1 != k2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:52:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (8210)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (8225)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (8204)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (8209)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (8225)Refutation not found, incomplete strategy% (8225)------------------------------
% 0.21/0.49  % (8225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8225)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (8225)Memory used [KB]: 10490
% 0.21/0.49  % (8225)Time elapsed: 0.078 s
% 0.21/0.49  % (8225)------------------------------
% 0.21/0.49  % (8225)------------------------------
% 0.21/0.49  % (8212)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (8219)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (8208)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (8206)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (8210)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1501,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f24,f28,f32,f45,f66,f117,f124,f260,f1500])).
% 0.21/0.50  fof(f1500,plain,(
% 0.21/0.50    spl3_1 | ~spl3_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f1498,f249,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    spl3_1 <=> sK1 = k2_xboole_0(sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    spl3_17 <=> sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.50  fof(f1498,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(sK0,sK2) | ~spl3_17),
% 0.21/0.50    inference(forward_demodulation,[],[f1497,f250])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | ~spl3_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f249])).
% 0.21/0.50  fof(f1497,plain,(
% 0.21/0.50    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f1492,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.50  fof(f1492,plain,(
% 0.21/0.50    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 0.21/0.50    inference(resolution,[],[f181,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(superposition,[],[f17,f18])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK0,k2_xboole_0(sK2,X0)) | k2_xboole_0(sK2,X0) = k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) )),
% 0.21/0.50    inference(resolution,[],[f39,f17])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK2,X0) | k2_xboole_0(sK1,X0) = X0 | ~r1_tarski(sK0,X0)) )),
% 0.21/0.50    inference(resolution,[],[f19,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ( ! [X3] : (r1_tarski(sK1,X3) | ~r1_tarski(sK2,X3) | ~r1_tarski(sK0,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    sK1 != k2_xboole_0(sK0,sK2) & ! [X3] : (r1_tarski(sK1,X3) | ~r1_tarski(sK2,X3) | ~r1_tarski(sK0,X3)) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (k2_xboole_0(X0,X2) != X1 & ! [X3] : (r1_tarski(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (sK1 != k2_xboole_0(sK0,sK2) & ! [X3] : (r1_tarski(sK1,X3) | ~r1_tarski(sK2,X3) | ~r1_tarski(sK0,X3)) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (k2_xboole_0(X0,X2) != X1 & ! [X3] : (r1_tarski(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (k2_xboole_0(X0,X2) != X1 & (! [X3] : (r1_tarski(X1,X3) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X3))) & r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    spl3_17 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f246,f122,f249])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl3_12 <=> sK1 = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | ~spl3_12),
% 0.21/0.50    inference(superposition,[],[f18,f123])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1) | ~spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f122])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl3_12 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f120,f115,f122])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl3_11 <=> r1_tarski(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1) | ~spl3_11),
% 0.21/0.50    inference(resolution,[],[f116,f19])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    r1_tarski(k2_xboole_0(sK0,sK2),sK1) | ~spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl3_11 | ~spl3_3 | ~spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f110,f57,f30,f115])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl3_6 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    r1_tarski(k2_xboole_0(sK0,sK2),sK1) | (~spl3_3 | ~spl3_6)),
% 0.21/0.50    inference(superposition,[],[f77,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(sK1,sK2) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f57])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(k2_xboole_0(sK0,X1),k2_xboole_0(sK1,X1))) ) | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f20,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f30])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl3_6 | ~spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f43,f57])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    spl3_4 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(sK1,sK2) | ~spl3_4),
% 0.21/0.50    inference(superposition,[],[f18,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(sK2,sK1) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f43])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl3_4 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f26,f43])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(sK2,sK1) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f19,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f26])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f13,f30])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f14,f26])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    r1_tarski(sK2,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ~spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f16,f22])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    sK1 != k2_xboole_0(sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8210)------------------------------
% 0.21/0.50  % (8210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8210)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8210)Memory used [KB]: 11385
% 0.21/0.50  % (8210)Time elapsed: 0.088 s
% 0.21/0.50  % (8210)------------------------------
% 0.21/0.50  % (8210)------------------------------
% 0.21/0.50  % (8217)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (8211)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (8200)Success in time 0.147 s
%------------------------------------------------------------------------------
