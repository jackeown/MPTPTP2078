%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:38 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 110 expanded)
%              Number of leaves         :   13 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  159 ( 236 expanded)
%              Number of equality atoms :   68 ( 117 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f118,f164,f1194,f1215,f1241])).

fof(f1241,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f1224])).

fof(f1224,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f96,f87,f1208])).

fof(f1208,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
        | ~ r2_hidden(X4,sK0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f80,f91])).

fof(f91,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_1
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f87,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f96,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1215,plain,
    ( sK1 != sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0)
    | r2_hidden(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1194,plain,
    ( spl6_8
    | ~ spl6_4
    | spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f828,f161,f90,f161,f1191])).

fof(f1191,plain,
    ( spl6_8
  <=> sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f161,plain,
    ( spl6_4
  <=> r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f828,plain,
    ( ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0)
    | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | spl6_1
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f822])).

fof(f822,plain,
    ( ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0)
    | sK0 != sK0
    | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f223,f163])).

fof(f163,plain,
    ( r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f161])).

fof(f223,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),sK0)
        | ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),X1)
        | sK0 != X1
        | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1) )
    | spl6_1 ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( ! [X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),X1)
        | ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),sK0)
        | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1)
        | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1)
        | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1) )
    | spl6_1 ),
    inference(resolution,[],[f102,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
        | sK0 != X0
        | ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),X0)
        | ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),sK0) )
    | spl6_1 ),
    inference(superposition,[],[f92,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f38,f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f92,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f164,plain,
    ( spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f159,f90,f161])).

fof(f159,plain,
    ( r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0)
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0)
    | sK0 != sK0
    | spl6_1 ),
    inference(factoring,[],[f103])).

fof(f103,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),sK0)
        | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),X1)
        | sK0 != X1 )
    | spl6_1 ),
    inference(superposition,[],[f92,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f39,f27])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f118,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f57,f94,f90])).

fof(f57,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f20,f27,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f53])).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f97,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f56,f94,f90])).

fof(f56,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f21,f27,f55])).

fof(f21,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:22:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (32531)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (32539)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (32526)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (32532)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (32547)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (32547)Refutation not found, incomplete strategy% (32547)------------------------------
% 0.20/0.51  % (32547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32530)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (32547)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32547)Memory used [KB]: 1791
% 0.20/0.52  % (32547)Time elapsed: 0.105 s
% 0.20/0.52  % (32547)------------------------------
% 0.20/0.52  % (32547)------------------------------
% 0.20/0.52  % (32536)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (32555)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (32540)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (32549)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (32537)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (32529)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (32541)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (32542)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (32554)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (32527)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (32548)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (32553)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (32533)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (32550)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (32535)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (32545)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (32534)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (32546)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (32534)Refutation not found, incomplete strategy% (32534)------------------------------
% 0.20/0.55  % (32534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (32534)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (32534)Memory used [KB]: 10618
% 0.20/0.55  % (32534)Time elapsed: 0.140 s
% 0.20/0.55  % (32534)------------------------------
% 0.20/0.55  % (32534)------------------------------
% 0.20/0.55  % (32551)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (32552)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (32538)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (32544)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (32528)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.57  % (32528)Refutation not found, incomplete strategy% (32528)------------------------------
% 0.20/0.57  % (32528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (32528)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (32528)Memory used [KB]: 10746
% 0.20/0.57  % (32528)Time elapsed: 0.136 s
% 0.20/0.57  % (32528)------------------------------
% 0.20/0.57  % (32528)------------------------------
% 0.20/0.58  % (32543)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.58  % (32543)Refutation not found, incomplete strategy% (32543)------------------------------
% 0.20/0.58  % (32543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (32543)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (32543)Memory used [KB]: 10618
% 0.20/0.58  % (32543)Time elapsed: 0.144 s
% 0.20/0.58  % (32543)------------------------------
% 0.20/0.58  % (32543)------------------------------
% 1.94/0.62  % (32548)Refutation found. Thanks to Tanya!
% 1.94/0.62  % SZS status Theorem for theBenchmark
% 1.94/0.62  % SZS output start Proof for theBenchmark
% 1.94/0.62  fof(f1242,plain,(
% 1.94/0.62    $false),
% 1.94/0.62    inference(avatar_sat_refutation,[],[f97,f118,f164,f1194,f1215,f1241])).
% 1.94/0.62  fof(f1241,plain,(
% 1.94/0.62    ~spl6_1 | ~spl6_2),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f1224])).
% 1.94/0.62  fof(f1224,plain,(
% 1.94/0.62    $false | (~spl6_1 | ~spl6_2)),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f96,f87,f1208])).
% 1.94/0.62  fof(f1208,plain,(
% 1.94/0.62    ( ! [X4] : (~r2_hidden(X4,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X4,sK0)) ) | ~spl6_1),
% 1.94/0.62    inference(superposition,[],[f80,f91])).
% 1.94/0.62  fof(f91,plain,(
% 1.94/0.62    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl6_1),
% 1.94/0.62    inference(avatar_component_clause,[],[f90])).
% 1.94/0.62  fof(f90,plain,(
% 1.94/0.62    spl6_1 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.94/0.62  fof(f80,plain,(
% 1.94/0.62    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.94/0.62    inference(equality_resolution,[],[f63])).
% 1.94/0.62  fof(f63,plain,(
% 1.94/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.94/0.62    inference(definition_unfolding,[],[f42,f27])).
% 1.94/0.62  fof(f27,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f5])).
% 1.94/0.62  fof(f5,axiom,(
% 1.94/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.94/0.62  fof(f42,plain,(
% 1.94/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.94/0.62    inference(cnf_transformation,[],[f3])).
% 1.94/0.62  fof(f3,axiom,(
% 1.94/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.94/0.62  fof(f87,plain,(
% 1.94/0.62    ( ! [X4,X2,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2))) )),
% 1.94/0.62    inference(equality_resolution,[],[f86])).
% 1.94/0.62  fof(f86,plain,(
% 1.94/0.62    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X4,X4,X4,X1,X2) != X3) )),
% 1.94/0.62    inference(equality_resolution,[],[f70])).
% 1.94/0.62  fof(f70,plain,(
% 1.94/0.62    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.94/0.62    inference(definition_unfolding,[],[f50,f53])).
% 1.94/0.62  fof(f53,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.94/0.62    inference(definition_unfolding,[],[f31,f44])).
% 1.94/0.62  fof(f44,plain,(
% 1.94/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f12])).
% 1.94/0.62  fof(f12,axiom,(
% 1.94/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.94/0.62  fof(f31,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f11])).
% 1.94/0.62  fof(f11,axiom,(
% 1.94/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.94/0.62  fof(f50,plain,(
% 1.94/0.62    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.94/0.62    inference(cnf_transformation,[],[f19])).
% 1.94/0.62  fof(f19,plain,(
% 1.94/0.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.94/0.62    inference(ennf_transformation,[],[f8])).
% 1.94/0.62  fof(f8,axiom,(
% 1.94/0.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.94/0.62  fof(f96,plain,(
% 1.94/0.62    r2_hidden(sK1,sK0) | ~spl6_2),
% 1.94/0.62    inference(avatar_component_clause,[],[f94])).
% 1.94/0.62  fof(f94,plain,(
% 1.94/0.62    spl6_2 <=> r2_hidden(sK1,sK0)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.94/0.62  fof(f1215,plain,(
% 1.94/0.62    sK1 != sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | ~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0) | r2_hidden(sK1,sK0)),
% 1.94/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.94/0.62  fof(f1194,plain,(
% 1.94/0.62    spl6_8 | ~spl6_4 | spl6_1 | ~spl6_4),
% 1.94/0.62    inference(avatar_split_clause,[],[f828,f161,f90,f161,f1191])).
% 1.94/0.62  fof(f1191,plain,(
% 1.94/0.62    spl6_8 <=> sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.94/0.62  fof(f161,plain,(
% 1.94/0.62    spl6_4 <=> r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.94/0.62  fof(f828,plain,(
% 1.94/0.62    ~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0) | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | (spl6_1 | ~spl6_4)),
% 1.94/0.62    inference(trivial_inequality_removal,[],[f822])).
% 1.94/0.62  fof(f822,plain,(
% 1.94/0.62    ~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0) | sK0 != sK0 | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | (spl6_1 | ~spl6_4)),
% 1.94/0.62    inference(resolution,[],[f223,f163])).
% 1.94/0.62  fof(f163,plain,(
% 1.94/0.62    r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0) | ~spl6_4),
% 1.94/0.62    inference(avatar_component_clause,[],[f161])).
% 1.94/0.62  fof(f223,plain,(
% 1.94/0.62    ( ! [X1] : (~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),sK0) | ~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),X1) | sK0 != X1 | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1)) ) | spl6_1),
% 1.94/0.62    inference(duplicate_literal_removal,[],[f217])).
% 1.94/0.62  fof(f217,plain,(
% 1.94/0.62    ( ! [X1] : (sK0 != X1 | ~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),X1) | ~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),sK0) | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1) | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1) | sK1 = sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1)) ) | spl6_1),
% 1.94/0.62    inference(resolution,[],[f102,f88])).
% 1.94/0.62  fof(f88,plain,(
% 1.94/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.94/0.62    inference(equality_resolution,[],[f71])).
% 1.94/0.62  fof(f71,plain,(
% 1.94/0.62    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.94/0.62    inference(definition_unfolding,[],[f49,f53])).
% 1.94/0.62  fof(f49,plain,(
% 1.94/0.62    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.94/0.62    inference(cnf_transformation,[],[f19])).
% 1.94/0.62  fof(f102,plain,(
% 1.94/0.62    ( ! [X0] : (r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | sK0 != X0 | ~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),X0) | ~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),sK0)) ) | spl6_1),
% 1.94/0.62    inference(superposition,[],[f92,f67])).
% 1.94/0.62  fof(f67,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0)) )),
% 1.94/0.62    inference(definition_unfolding,[],[f38,f27])).
% 1.94/0.62  fof(f38,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.94/0.62    inference(cnf_transformation,[],[f3])).
% 1.94/0.62  fof(f92,plain,(
% 1.94/0.62    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl6_1),
% 1.94/0.62    inference(avatar_component_clause,[],[f90])).
% 1.94/0.62  fof(f164,plain,(
% 1.94/0.62    spl6_4 | spl6_1),
% 1.94/0.62    inference(avatar_split_clause,[],[f159,f90,f161])).
% 1.94/0.62  fof(f159,plain,(
% 1.94/0.62    r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0) | spl6_1),
% 1.94/0.62    inference(trivial_inequality_removal,[],[f153])).
% 1.94/0.62  fof(f153,plain,(
% 1.94/0.62    r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),sK0) | sK0 != sK0 | spl6_1),
% 1.94/0.62    inference(factoring,[],[f103])).
% 1.94/0.62  fof(f103,plain,(
% 1.94/0.62    ( ! [X1] : (r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),sK0) | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),X1) | sK0 != X1) ) | spl6_1),
% 1.94/0.62    inference(superposition,[],[f92,f66])).
% 1.94/0.62  fof(f66,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0)) )),
% 1.94/0.62    inference(definition_unfolding,[],[f39,f27])).
% 1.94/0.62  fof(f39,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.94/0.62    inference(cnf_transformation,[],[f3])).
% 1.94/0.62  fof(f118,plain,(
% 1.94/0.62    spl6_1 | ~spl6_2),
% 1.94/0.62    inference(avatar_split_clause,[],[f57,f94,f90])).
% 1.94/0.62  fof(f57,plain,(
% 1.94/0.62    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.94/0.62    inference(definition_unfolding,[],[f20,f27,f55])).
% 1.94/0.62  fof(f55,plain,(
% 1.94/0.62    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.94/0.62    inference(definition_unfolding,[],[f23,f54])).
% 1.94/0.62  fof(f54,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.94/0.62    inference(definition_unfolding,[],[f26,f53])).
% 1.94/0.62  fof(f26,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f10])).
% 1.94/0.62  fof(f10,axiom,(
% 1.94/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.94/0.62  fof(f23,plain,(
% 1.94/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f9])).
% 1.94/0.62  fof(f9,axiom,(
% 1.94/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.94/0.62  fof(f20,plain,(
% 1.94/0.62    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.94/0.62    inference(cnf_transformation,[],[f16])).
% 1.94/0.62  fof(f16,plain,(
% 1.94/0.62    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.94/0.62    inference(ennf_transformation,[],[f15])).
% 1.94/0.62  fof(f15,negated_conjecture,(
% 1.94/0.62    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.94/0.62    inference(negated_conjecture,[],[f14])).
% 1.94/0.62  fof(f14,conjecture,(
% 1.94/0.62    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.94/0.62  fof(f97,plain,(
% 1.94/0.62    ~spl6_1 | spl6_2),
% 1.94/0.62    inference(avatar_split_clause,[],[f56,f94,f90])).
% 1.94/0.62  fof(f56,plain,(
% 1.94/0.62    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.94/0.62    inference(definition_unfolding,[],[f21,f27,f55])).
% 1.94/0.62  fof(f21,plain,(
% 1.94/0.62    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.94/0.62    inference(cnf_transformation,[],[f16])).
% 1.94/0.62  % SZS output end Proof for theBenchmark
% 1.94/0.62  % (32548)------------------------------
% 1.94/0.62  % (32548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.62  % (32548)Termination reason: Refutation
% 1.94/0.62  
% 1.94/0.62  % (32548)Memory used [KB]: 11513
% 1.94/0.62  % (32548)Time elapsed: 0.204 s
% 1.94/0.62  % (32548)------------------------------
% 1.94/0.62  % (32548)------------------------------
% 1.94/0.63  % (32525)Success in time 0.252 s
%------------------------------------------------------------------------------
