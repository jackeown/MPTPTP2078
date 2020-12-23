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
% DateTime   : Thu Dec  3 12:55:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 297 expanded)
%              Number of leaves         :   18 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  242 ( 978 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f108,f128,f132,f152,f164,f192,f236])).

fof(f236,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f202,f223])).

fof(f223,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f44,f77])).

fof(f77,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_1
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,(
    r2_hidden(sK2(sK0,sK1),sK0) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f42,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f30,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_xboole_0(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r3_xboole_0(sK0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ~ r3_xboole_0(sK0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r3_xboole_0(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => r3_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => r3_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_ordinal1)).

fof(f202,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f124,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f124,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f192,plain,(
    ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl3_10 ),
    inference(resolution,[],[f173,f32])).

fof(f32,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

fof(f173,plain,
    ( ~ r3_xboole_0(sK0,sK0)
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f30,f123])).

fof(f123,plain,
    ( sK0 = sK1
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f164,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | spl3_10
    | spl3_2
    | spl3_7 ),
    inference(avatar_split_clause,[],[f162,f106,f79,f122,f116,f119])).

fof(f119,plain,
    ( spl3_9
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f116,plain,
    ( spl3_8
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f106,plain,
    ( spl3_7
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f162,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl3_7 ),
    inference(resolution,[],[f107,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f107,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f152,plain,
    ( spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f80,f133])).

fof(f133,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f45,f104])).

fof(f104,plain,
    ( sK0 = sK2(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_6
  <=> sK0 = sK2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f45,plain,(
    r2_hidden(sK2(sK1,sK0),sK1) ),
    inference(resolution,[],[f43,f36])).

fof(f43,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f132,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f28,f120])).

fof(f120,plain,
    ( ~ v3_ordinal1(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f28,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f128,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl3_8 ),
    inference(subsumption_resolution,[],[f29,f117])).

fof(f117,plain,
    ( ~ v3_ordinal1(sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f29,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,
    ( spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f101,f106,f103])).

fof(f101,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = sK2(sK1,sK0) ),
    inference(global_subsumption,[],[f28,f43,f93])).

fof(f93,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = sK2(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f64,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,sK0),X0)
      | ~ r2_hidden(sK1,X0)
      | sK2(sK1,sK0) = X0
      | ~ v3_ordinal1(X0) ) ),
    inference(global_subsumption,[],[f53,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | r2_hidden(sK2(sK1,sK0),X0)
      | sK2(sK1,sK0) = X0
      | ~ v3_ordinal1(sK2(sK1,sK0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f50,f31])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2(sK1,sK0))
      | ~ r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f45,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_ordinal1)).

fof(f53,plain,(
    v3_ordinal1(sK2(sK1,sK0)) ),
    inference(global_subsumption,[],[f29,f52])).

fof(f52,plain,
    ( v3_ordinal1(sK2(sK1,sK0))
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f45,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f81,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f74,f79,f76])).

fof(f74,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = sK2(sK0,sK1) ),
    inference(global_subsumption,[],[f29,f42,f66])).

fof(f66,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = sK2(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f60,f37])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,sK1),X0)
      | ~ r2_hidden(sK0,X0)
      | sK2(sK0,sK1) = X0
      | ~ v3_ordinal1(X0) ) ),
    inference(global_subsumption,[],[f49,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r2_hidden(sK2(sK0,sK1),X0)
      | sK2(sK0,sK1) = X0
      | ~ v3_ordinal1(sK2(sK0,sK1))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f46,f31])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2(sK0,sK1))
      | ~ r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f44,f41])).

fof(f49,plain,(
    v3_ordinal1(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f28,f48])).

fof(f48,plain,
    ( v3_ordinal1(sK2(sK0,sK1))
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f44,f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:53:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (8846)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (8838)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (8839)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (8836)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (8855)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (8861)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (8855)Refutation not found, incomplete strategy% (8855)------------------------------
% 0.21/0.53  % (8855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8837)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (8855)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8855)Memory used [KB]: 10618
% 0.21/0.54  % (8855)Time elapsed: 0.126 s
% 0.21/0.54  % (8855)------------------------------
% 0.21/0.54  % (8855)------------------------------
% 0.21/0.54  % (8833)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (8833)Refutation not found, incomplete strategy% (8833)------------------------------
% 0.21/0.54  % (8833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8833)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8833)Memory used [KB]: 1663
% 0.21/0.54  % (8833)Time elapsed: 0.124 s
% 0.21/0.54  % (8833)------------------------------
% 0.21/0.54  % (8833)------------------------------
% 0.21/0.54  % (8860)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (8859)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (8835)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (8834)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (8862)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (8843)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (8851)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (8849)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (8845)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (8835)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f237,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f81,f108,f128,f132,f152,f164,f192,f236])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    ~spl3_1 | ~spl3_2),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f232])).
% 0.21/0.55  fof(f232,plain,(
% 0.21/0.55    $false | (~spl3_1 | ~spl3_2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f202,f223])).
% 0.21/0.55  fof(f223,plain,(
% 0.21/0.55    r2_hidden(sK1,sK0) | ~spl3_1),
% 0.21/0.55    inference(backward_demodulation,[],[f44,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    sK1 = sK2(sK0,sK1) | ~spl3_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    spl3_1 <=> sK1 = sK2(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    r2_hidden(sK2(sK0,sK1),sK0)),
% 0.21/0.55    inference(resolution,[],[f42,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ~r1_tarski(sK0,sK1)),
% 0.21/0.55    inference(resolution,[],[f30,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & (r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~r3_xboole_0(X0,X1)))),
% 0.21/0.55    inference(flattening,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) | ~r3_xboole_0(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ~r3_xboole_0(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    (~r3_xboole_0(sK0,sK1) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20,f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (~r3_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (~r3_xboole_0(sK0,X1) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ? [X1] : (~r3_xboole_0(sK0,X1) & v3_ordinal1(X1)) => (~r3_xboole_0(sK0,sK1) & v3_ordinal1(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (~r3_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => r3_xboole_0(X0,X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f8])).
% 0.21/0.55  fof(f8,conjecture,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => r3_xboole_0(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_ordinal1)).
% 0.21/0.55  fof(f202,plain,(
% 0.21/0.55    ~r2_hidden(sK1,sK0) | ~spl3_2),
% 0.21/0.55    inference(resolution,[],[f124,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1) | ~spl3_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    spl3_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    ~spl3_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    $false | ~spl3_10),
% 0.21/0.55    inference(resolution,[],[f173,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X0] : (r3_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0] : r3_xboole_0(X0,X0)),
% 0.21/0.55    inference(rectify,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : r3_xboole_0(X0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).
% 0.21/0.55  fof(f173,plain,(
% 0.21/0.55    ~r3_xboole_0(sK0,sK0) | ~spl3_10),
% 0.21/0.55    inference(backward_demodulation,[],[f30,f123])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    sK0 = sK1 | ~spl3_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f122])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    spl3_10 <=> sK0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    ~spl3_9 | ~spl3_8 | spl3_10 | spl3_2 | spl3_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f162,f106,f79,f122,f116,f119])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    spl3_9 <=> v3_ordinal1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    spl3_8 <=> v3_ordinal1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    spl3_7 <=> r2_hidden(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl3_7),
% 0.21/0.55    inference(resolution,[],[f107,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ~r2_hidden(sK1,sK0) | spl3_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f106])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    spl3_2 | ~spl3_6),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    $false | (spl3_2 | ~spl3_6)),
% 0.21/0.55    inference(subsumption_resolution,[],[f80,f133])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1) | ~spl3_6),
% 0.21/0.55    inference(backward_demodulation,[],[f45,f104])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    sK0 = sK2(sK1,sK0) | ~spl3_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f103])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    spl3_6 <=> sK0 = sK2(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    r2_hidden(sK2(sK1,sK0),sK1)),
% 0.21/0.55    inference(resolution,[],[f43,f36])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ~r1_tarski(sK1,sK0)),
% 0.21/0.55    inference(resolution,[],[f30,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ~r2_hidden(sK0,sK1) | spl3_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f79])).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    spl3_9),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f131])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    $false | spl3_9),
% 0.21/0.55    inference(subsumption_resolution,[],[f28,f120])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    ~v3_ordinal1(sK0) | spl3_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f119])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    v3_ordinal1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    spl3_8),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    $false | spl3_8),
% 0.21/0.55    inference(subsumption_resolution,[],[f29,f117])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ~v3_ordinal1(sK1) | spl3_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f116])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    v3_ordinal1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    spl3_6 | ~spl3_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f101,f106,f103])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ~r2_hidden(sK1,sK0) | sK0 = sK2(sK1,sK0)),
% 0.21/0.55    inference(global_subsumption,[],[f28,f43,f93])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ~r2_hidden(sK1,sK0) | sK0 = sK2(sK1,sK0) | ~v3_ordinal1(sK0) | r1_tarski(sK1,sK0)),
% 0.21/0.55    inference(resolution,[],[f64,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK2(sK1,sK0),X0) | ~r2_hidden(sK1,X0) | sK2(sK1,sK0) = X0 | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(global_subsumption,[],[f53,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK1,X0) | r2_hidden(sK2(sK1,sK0),X0) | sK2(sK1,sK0) = X0 | ~v3_ordinal1(sK2(sK1,sK0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(resolution,[],[f50,f31])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK2(sK1,sK0)) | ~r2_hidden(sK1,X0)) )),
% 0.21/0.55    inference(resolution,[],[f45,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ~(r2_hidden(X2,X0) & r2_hidden(X1,X2) & r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_ordinal1)).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    v3_ordinal1(sK2(sK1,sK0))),
% 0.21/0.55    inference(global_subsumption,[],[f29,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    v3_ordinal1(sK2(sK1,sK0)) | ~v3_ordinal1(sK1)),
% 0.21/0.55    inference(resolution,[],[f45,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.55    inference(flattening,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    spl3_1 | ~spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f74,f79,f76])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ~r2_hidden(sK0,sK1) | sK1 = sK2(sK0,sK1)),
% 0.21/0.55    inference(global_subsumption,[],[f29,f42,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ~r2_hidden(sK0,sK1) | sK1 = sK2(sK0,sK1) | ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.55    inference(resolution,[],[f60,f37])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK2(sK0,sK1),X0) | ~r2_hidden(sK0,X0) | sK2(sK0,sK1) = X0 | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(global_subsumption,[],[f49,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(sK2(sK0,sK1),X0) | sK2(sK0,sK1) = X0 | ~v3_ordinal1(sK2(sK0,sK1)) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(resolution,[],[f46,f31])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK2(sK0,sK1)) | ~r2_hidden(sK0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f44,f41])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    v3_ordinal1(sK2(sK0,sK1))),
% 0.21/0.55    inference(global_subsumption,[],[f28,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    v3_ordinal1(sK2(sK0,sK1)) | ~v3_ordinal1(sK0)),
% 0.21/0.55    inference(resolution,[],[f44,f33])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (8835)------------------------------
% 0.21/0.55  % (8835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8835)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (8835)Memory used [KB]: 10746
% 0.21/0.55  % (8835)Time elapsed: 0.141 s
% 0.21/0.55  % (8835)------------------------------
% 0.21/0.55  % (8835)------------------------------
% 0.21/0.55  % (8844)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (8832)Success in time 0.185 s
%------------------------------------------------------------------------------
