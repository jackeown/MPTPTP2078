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
% DateTime   : Thu Dec  3 12:55:25 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 197 expanded)
%              Number of leaves         :   13 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 ( 525 expanded)
%              Number of equality atoms :   11 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f104,f202,f327])).

fof(f327,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f254,f47,f267,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f267,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f228,f240])).

fof(f240,plain,
    ( sK0 = sK1
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f25,f26,f79,f227,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f227,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f223,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f223,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f214,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f214,plain,
    ( r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f25,f57,f82,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

% (30207)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f82,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_2
  <=> r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,(
    v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f26,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f79,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f26,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f25,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f228,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f223,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f254,plain,
    ( ~ r2_hidden(sK0,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f79,f240])).

fof(f202,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f190])).

% (30204)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (30196)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f190,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f110,f135,f129,f50])).

fof(f129,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f25,f57,f83,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f83,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f135,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f107,f35])).

fof(f107,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f78,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f78,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f110,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f78,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

% (30194)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f104,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f45,f81,f77])).

% (30195)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (30197)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (30199)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (30205)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f45,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f23,f31])).

fof(f23,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f44,f81,f77])).

fof(f44,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f24,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (30186)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.49  % (30202)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.49  % (30179)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.50  % (30192)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.51  % (30208)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.22/0.51  % (30200)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.22/0.51  % (30183)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.51  % (30201)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.52  % (30193)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.52  % (30187)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.52  % (30198)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.25/0.52  % (30201)Refutation not found, incomplete strategy% (30201)------------------------------
% 1.25/0.52  % (30201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (30201)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (30201)Memory used [KB]: 10746
% 1.25/0.52  % (30201)Time elapsed: 0.071 s
% 1.25/0.52  % (30201)------------------------------
% 1.25/0.52  % (30201)------------------------------
% 1.25/0.53  % (30181)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.53  % (30185)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.53  % (30184)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.53  % (30181)Refutation not found, incomplete strategy% (30181)------------------------------
% 1.25/0.53  % (30181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (30181)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (30181)Memory used [KB]: 10746
% 1.25/0.53  % (30181)Time elapsed: 0.116 s
% 1.25/0.53  % (30181)------------------------------
% 1.25/0.53  % (30181)------------------------------
% 1.25/0.53  % (30190)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.25/0.53  % (30180)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.53  % (30206)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.53  % (30182)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.53  % (30183)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f328,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(avatar_sat_refutation,[],[f84,f104,f202,f327])).
% 1.25/0.53  fof(f327,plain,(
% 1.25/0.53    spl3_1 | ~spl3_2),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f322])).
% 1.25/0.53  fof(f322,plain,(
% 1.25/0.53    $false | (spl3_1 | ~spl3_2)),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f254,f47,f267,f50])).
% 1.25/0.53  fof(f50,plain,(
% 1.25/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 1.25/0.53    inference(equality_resolution,[],[f41])).
% 1.25/0.53  fof(f41,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.25/0.53  fof(f267,plain,(
% 1.25/0.53    ~r2_hidden(sK0,k1_tarski(sK0)) | (spl3_1 | ~spl3_2)),
% 1.25/0.53    inference(backward_demodulation,[],[f228,f240])).
% 1.25/0.53  fof(f240,plain,(
% 1.25/0.53    sK0 = sK1 | (spl3_1 | ~spl3_2)),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f25,f26,f79,f227,f34])).
% 1.25/0.53  fof(f34,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f21])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.25/0.53    inference(flattening,[],[f20])).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f7])).
% 1.25/0.53  fof(f7,axiom,(
% 1.25/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.25/0.53  fof(f227,plain,(
% 1.25/0.53    ~r2_hidden(sK1,sK0) | ~spl3_2),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f223,f49])).
% 1.25/0.53  fof(f49,plain,(
% 1.25/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.25/0.53    inference(equality_resolution,[],[f42])).
% 1.25/0.53  fof(f42,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f223,plain,(
% 1.25/0.53    ~r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl3_2),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f214,f35])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f22])).
% 1.25/0.53  fof(f22,plain,(
% 1.25/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f10])).
% 1.25/0.53  fof(f10,axiom,(
% 1.25/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.25/0.53  fof(f214,plain,(
% 1.25/0.53    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~spl3_2),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f25,f57,f82,f28])).
% 1.25/0.53  fof(f28,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f15])).
% 1.25/0.53  fof(f15,plain,(
% 1.25/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.25/0.53    inference(flattening,[],[f14])).
% 1.25/0.53  fof(f14,plain,(
% 1.25/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.25/0.53    inference(ennf_transformation,[],[f5])).
% 1.25/0.53  % (30207)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.25/0.53  fof(f5,axiom,(
% 1.25/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.25/0.53  fof(f82,plain,(
% 1.25/0.53    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~spl3_2),
% 1.25/0.53    inference(avatar_component_clause,[],[f81])).
% 1.25/0.53  fof(f81,plain,(
% 1.25/0.53    spl3_2 <=> r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.25/0.53  fof(f57,plain,(
% 1.25/0.53    v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f26,f46])).
% 1.25/0.53  fof(f46,plain,(
% 1.25/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f30,f31])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.25/0.53  fof(f30,plain,(
% 1.25/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f18,plain,(
% 1.25/0.53    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f9])).
% 1.25/0.53  fof(f9,axiom,(
% 1.25/0.53    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 1.25/0.53  fof(f79,plain,(
% 1.25/0.53    ~r2_hidden(sK0,sK1) | spl3_1),
% 1.25/0.53    inference(avatar_component_clause,[],[f77])).
% 1.25/0.53  fof(f77,plain,(
% 1.25/0.53    spl3_1 <=> r2_hidden(sK0,sK1)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    v3_ordinal1(sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f13])).
% 1.25/0.53  fof(f13,plain,(
% 1.25/0.53    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f12])).
% 1.25/0.53  fof(f12,negated_conjecture,(
% 1.25/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.25/0.53    inference(negated_conjecture,[],[f11])).
% 1.25/0.53  fof(f11,conjecture,(
% 1.25/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    v3_ordinal1(sK1)),
% 1.25/0.53    inference(cnf_transformation,[],[f13])).
% 1.25/0.53  fof(f228,plain,(
% 1.25/0.53    ~r2_hidden(sK1,k1_tarski(sK0)) | ~spl3_2),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f223,f48])).
% 1.25/0.53  fof(f48,plain,(
% 1.25/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.25/0.53    inference(equality_resolution,[],[f43])).
% 1.25/0.53  fof(f43,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f47,plain,(
% 1.25/0.53    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f32,f31])).
% 1.25/0.53  fof(f32,plain,(
% 1.25/0.53    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,axiom,(
% 1.25/0.53    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.25/0.53  fof(f254,plain,(
% 1.25/0.53    ~r2_hidden(sK0,sK0) | (spl3_1 | ~spl3_2)),
% 1.25/0.53    inference(backward_demodulation,[],[f79,f240])).
% 1.25/0.53  fof(f202,plain,(
% 1.25/0.53    ~spl3_1 | spl3_2),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f190])).
% 1.25/0.53  % (30204)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.25/0.54  % (30196)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.54  fof(f190,plain,(
% 1.25/0.54    $false | (~spl3_1 | spl3_2)),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f110,f135,f129,f50])).
% 1.25/0.54  fof(f129,plain,(
% 1.25/0.54    r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | spl3_2),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f25,f57,f83,f29])).
% 1.25/0.54  fof(f29,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f17])).
% 1.25/0.54  fof(f17,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.25/0.54    inference(flattening,[],[f16])).
% 1.25/0.54  fof(f16,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.25/0.54    inference(ennf_transformation,[],[f8])).
% 1.25/0.54  fof(f8,axiom,(
% 1.25/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.25/0.54  fof(f83,plain,(
% 1.25/0.54    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | spl3_2),
% 1.25/0.54    inference(avatar_component_clause,[],[f81])).
% 1.25/0.54  fof(f135,plain,(
% 1.25/0.54    ~r2_hidden(sK1,k1_tarski(sK0)) | ~spl3_1),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f107,f35])).
% 1.25/0.54  fof(f107,plain,(
% 1.25/0.54    r1_tarski(k1_tarski(sK0),sK1) | ~spl3_1),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f78,f36])).
% 1.25/0.54  fof(f36,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f3])).
% 1.25/0.54  fof(f3,axiom,(
% 1.25/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.25/0.54  fof(f78,plain,(
% 1.25/0.54    r2_hidden(sK0,sK1) | ~spl3_1),
% 1.25/0.54    inference(avatar_component_clause,[],[f77])).
% 1.25/0.54  fof(f110,plain,(
% 1.25/0.54    ~r2_hidden(sK1,sK0) | ~spl3_1),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f78,f33])).
% 1.25/0.54  fof(f33,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f19])).
% 1.25/0.54  % (30194)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.54  fof(f19,plain,(
% 1.25/0.54    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.25/0.54    inference(ennf_transformation,[],[f1])).
% 1.25/0.54  fof(f1,axiom,(
% 1.25/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.25/0.54  fof(f104,plain,(
% 1.25/0.54    spl3_1 | spl3_2),
% 1.25/0.54    inference(avatar_split_clause,[],[f45,f81,f77])).
% 1.25/0.54  % (30195)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.54  % (30197)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.54  % (30199)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.54  % (30205)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.54  fof(f45,plain,(
% 1.25/0.54    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | r2_hidden(sK0,sK1)),
% 1.25/0.54    inference(definition_unfolding,[],[f23,f31])).
% 1.25/0.54  fof(f23,plain,(
% 1.25/0.54    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.25/0.54    inference(cnf_transformation,[],[f13])).
% 1.25/0.54  fof(f84,plain,(
% 1.25/0.54    ~spl3_1 | ~spl3_2),
% 1.25/0.54    inference(avatar_split_clause,[],[f44,f81,f77])).
% 1.25/0.54  fof(f44,plain,(
% 1.25/0.54    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 1.25/0.54    inference(definition_unfolding,[],[f24,f31])).
% 1.25/0.54  fof(f24,plain,(
% 1.25/0.54    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 1.25/0.54    inference(cnf_transformation,[],[f13])).
% 1.25/0.54  % SZS output end Proof for theBenchmark
% 1.25/0.54  % (30183)------------------------------
% 1.25/0.54  % (30183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (30183)Termination reason: Refutation
% 1.25/0.54  
% 1.25/0.54  % (30183)Memory used [KB]: 6268
% 1.25/0.54  % (30183)Time elapsed: 0.115 s
% 1.25/0.54  % (30183)------------------------------
% 1.25/0.54  % (30183)------------------------------
% 1.25/0.54  % (30178)Success in time 0.185 s
%------------------------------------------------------------------------------
