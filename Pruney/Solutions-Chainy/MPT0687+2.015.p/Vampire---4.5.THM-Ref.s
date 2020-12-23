%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:39 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 181 expanded)
%              Number of leaves         :   14 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  151 ( 333 expanded)
%              Number of equality atoms :   56 ( 165 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f133,f240])).

fof(f240,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f25,f137,f90,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f90,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f137,plain,
    ( ! [X2,X0,X3,X1] : ~ r1_xboole_0(k2_relat_1(sK1),k5_enumset1(X0,X0,X0,X1,X2,sK0,X3))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f74,f135,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f135,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f134])).

fof(f134,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f57,f90])).

fof(f57,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f23,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X1] : r2_hidden(X6,k5_enumset1(X0,X0,X0,X1,X2,X6,X4)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( r2_hidden(X6,X5)
      | k5_enumset1(X0,X0,X0,X1,X2,X6,X4) != X5 ) ),
    inference(equality_resolution,[],[f60])).

% (32255)Refutation not found, incomplete strategy% (32255)------------------------------
% (32255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32255)Termination reason: Refutation not found, incomplete strategy

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X3 != X6
      | r2_hidden(X6,X5)
      | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f40,f51])).

% (32255)Memory used [KB]: 10746
% (32255)Time elapsed: 0.125 s
% (32255)------------------------------
% (32255)------------------------------
fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X3 != X6
      | r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f133,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f72,f92,f111,f42])).

fof(f111,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k2_relat_1(sK1))
    | spl4_1 ),
    inference(backward_demodulation,[],[f57,f108])).

fof(f108,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f94,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(sK1,X0)
      | ~ r1_xboole_0(k2_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f92,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f92,plain,
    ( r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f86,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f55])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f86,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f72,plain,(
    ! [X6,X2,X0,X3,X1] : r2_hidden(X6,k5_enumset1(X0,X0,X0,X1,X2,X3,X6)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( r2_hidden(X6,X5)
      | k5_enumset1(X0,X0,X0,X1,X2,X3,X6) != X5 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X4 != X6
      | r2_hidden(X6,X5)
      | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X4 != X6
      | r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f91,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f56,f88,f84])).

fof(f56,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f24,f55])).

fof(f24,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:05:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.47  % (32260)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.48  % (32276)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.52  % (32257)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.53  % (32266)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.53  % (32273)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.54  % (32265)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.54  % (32253)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.54  % (32275)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.54  % (32255)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (32256)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.54  % (32254)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.54  % (32257)Refutation found. Thanks to Tanya!
% 1.30/0.54  % SZS status Theorem for theBenchmark
% 1.30/0.54  % SZS output start Proof for theBenchmark
% 1.30/0.54  fof(f241,plain,(
% 1.30/0.54    $false),
% 1.30/0.54    inference(avatar_sat_refutation,[],[f91,f133,f240])).
% 1.30/0.54  fof(f240,plain,(
% 1.30/0.54    ~spl4_2),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f237])).
% 1.30/0.54  fof(f237,plain,(
% 1.30/0.54    $false | ~spl4_2),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f25,f137,f90,f27])).
% 1.30/0.54  fof(f27,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k10_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f18])).
% 1.30/0.54  fof(f18,plain,(
% 1.30/0.54    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.30/0.54    inference(ennf_transformation,[],[f13])).
% 1.30/0.54  fof(f13,axiom,(
% 1.30/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.30/0.54  fof(f90,plain,(
% 1.30/0.54    k1_xboole_0 = k10_relat_1(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_2),
% 1.30/0.54    inference(avatar_component_clause,[],[f88])).
% 1.30/0.54  fof(f88,plain,(
% 1.30/0.54    spl4_2 <=> k1_xboole_0 = k10_relat_1(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.30/0.54  fof(f137,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(k2_relat_1(sK1),k5_enumset1(X0,X0,X0,X1,X2,sK0,X3))) ) | ~spl4_2),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f74,f135,f42])).
% 1.30/0.54  fof(f42,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f21])).
% 1.30/0.54  fof(f21,plain,(
% 1.30/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.30/0.54    inference(ennf_transformation,[],[f16])).
% 1.30/0.54  fof(f16,plain,(
% 1.30/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.54    inference(rectify,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.30/0.54  fof(f135,plain,(
% 1.30/0.54    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl4_2),
% 1.30/0.54    inference(trivial_inequality_removal,[],[f134])).
% 1.30/0.54  fof(f134,plain,(
% 1.30/0.54    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,k2_relat_1(sK1)) | ~spl4_2),
% 1.30/0.54    inference(backward_demodulation,[],[f57,f90])).
% 1.30/0.54  fof(f57,plain,(
% 1.30/0.54    k1_xboole_0 != k10_relat_1(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 1.30/0.54    inference(definition_unfolding,[],[f23,f55])).
% 1.30/0.54  fof(f55,plain,(
% 1.30/0.54    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f29,f54])).
% 1.30/0.54  fof(f54,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f46,f53])).
% 1.30/0.54  fof(f53,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f49,f52])).
% 1.30/0.54  fof(f52,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f48,f51])).
% 1.30/0.54  fof(f51,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f47,f50])).
% 1.30/0.54  fof(f50,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.30/0.54  fof(f47,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f9])).
% 1.30/0.54  fof(f9,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.30/0.54  fof(f48,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f8])).
% 1.30/0.54  fof(f8,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,axiom,(
% 1.30/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.30/0.54  fof(f46,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f6])).
% 1.30/0.54  fof(f6,axiom,(
% 1.30/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.54  fof(f29,plain,(
% 1.30/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f5])).
% 1.30/0.54  fof(f5,axiom,(
% 1.30/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.30/0.54  fof(f23,plain,(
% 1.30/0.54    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 1.30/0.54    inference(cnf_transformation,[],[f17])).
% 1.30/0.54  fof(f17,plain,(
% 1.30/0.54    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 1.30/0.54    inference(ennf_transformation,[],[f15])).
% 1.30/0.54  fof(f15,negated_conjecture,(
% 1.30/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 1.30/0.54    inference(negated_conjecture,[],[f14])).
% 1.30/0.54  fof(f14,conjecture,(
% 1.30/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 1.30/0.54  fof(f74,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X1] : (r2_hidden(X6,k5_enumset1(X0,X0,X0,X1,X2,X6,X4))) )),
% 1.30/0.54    inference(equality_resolution,[],[f73])).
% 1.30/0.54  fof(f73,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X5,X1] : (r2_hidden(X6,X5) | k5_enumset1(X0,X0,X0,X1,X2,X6,X4) != X5) )),
% 1.30/0.54    inference(equality_resolution,[],[f60])).
% 1.30/0.54  % (32255)Refutation not found, incomplete strategy% (32255)------------------------------
% 1.30/0.54  % (32255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (32255)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  fof(f60,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X3 != X6 | r2_hidden(X6,X5) | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 1.30/0.54    inference(definition_unfolding,[],[f40,f51])).
% 1.30/0.54  % (32255)Memory used [KB]: 10746
% 1.30/0.54  % (32255)Time elapsed: 0.125 s
% 1.30/0.54  % (32255)------------------------------
% 1.30/0.54  % (32255)------------------------------
% 1.30/0.54  fof(f40,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X3 != X6 | r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.30/0.54    inference(cnf_transformation,[],[f20])).
% 1.30/0.54  fof(f20,plain,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.30/0.54    inference(ennf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 1.30/0.54  fof(f25,plain,(
% 1.30/0.54    v1_relat_1(sK1)),
% 1.30/0.54    inference(cnf_transformation,[],[f17])).
% 1.30/0.54  fof(f133,plain,(
% 1.30/0.54    spl4_1),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f128])).
% 1.30/0.54  fof(f128,plain,(
% 1.30/0.54    $false | spl4_1),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f72,f92,f111,f42])).
% 1.30/0.54  fof(f111,plain,(
% 1.30/0.54    r2_hidden(sK0,k2_relat_1(sK1)) | spl4_1),
% 1.30/0.54    inference(trivial_inequality_removal,[],[f110])).
% 1.30/0.54  fof(f110,plain,(
% 1.30/0.54    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,k2_relat_1(sK1)) | spl4_1),
% 1.30/0.54    inference(backward_demodulation,[],[f57,f108])).
% 1.30/0.54  fof(f108,plain,(
% 1.30/0.54    k1_xboole_0 = k10_relat_1(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl4_1),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f94,f82])).
% 1.30/0.54  fof(f82,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,X0) | ~r1_xboole_0(k2_relat_1(sK1),X0)) )),
% 1.30/0.54    inference(resolution,[],[f25,f26])).
% 1.30/0.54  fof(f26,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) = k1_xboole_0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f18])).
% 1.30/0.54  fof(f94,plain,(
% 1.30/0.54    r1_xboole_0(k2_relat_1(sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl4_1),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f92,f45])).
% 1.30/0.54  fof(f45,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f22])).
% 1.30/0.54  fof(f22,plain,(
% 1.30/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.30/0.54    inference(ennf_transformation,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.30/0.54  fof(f92,plain,(
% 1.30/0.54    r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1)) | spl4_1),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f86,f58])).
% 1.30/0.54  fof(f58,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f28,f55])).
% 1.30/0.54  fof(f28,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f19])).
% 1.30/0.54  fof(f19,plain,(
% 1.30/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.30/0.54    inference(ennf_transformation,[],[f11])).
% 1.30/0.54  fof(f11,axiom,(
% 1.30/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.30/0.54  fof(f86,plain,(
% 1.30/0.54    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl4_1),
% 1.30/0.54    inference(avatar_component_clause,[],[f84])).
% 1.30/0.54  fof(f84,plain,(
% 1.30/0.54    spl4_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.30/0.54  fof(f72,plain,(
% 1.30/0.54    ( ! [X6,X2,X0,X3,X1] : (r2_hidden(X6,k5_enumset1(X0,X0,X0,X1,X2,X3,X6))) )),
% 1.30/0.54    inference(equality_resolution,[],[f71])).
% 1.30/0.54  fof(f71,plain,(
% 1.30/0.54    ( ! [X6,X2,X0,X5,X3,X1] : (r2_hidden(X6,X5) | k5_enumset1(X0,X0,X0,X1,X2,X3,X6) != X5) )),
% 1.30/0.54    inference(equality_resolution,[],[f59])).
% 1.30/0.54  fof(f59,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X4 != X6 | r2_hidden(X6,X5) | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 1.30/0.54    inference(definition_unfolding,[],[f41,f51])).
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X4 != X6 | r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.30/0.54    inference(cnf_transformation,[],[f20])).
% 1.30/0.54  fof(f91,plain,(
% 1.30/0.54    ~spl4_1 | spl4_2),
% 1.30/0.54    inference(avatar_split_clause,[],[f56,f88,f84])).
% 1.30/0.54  fof(f56,plain,(
% 1.30/0.54    k1_xboole_0 = k10_relat_1(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.30/0.54    inference(definition_unfolding,[],[f24,f55])).
% 1.30/0.54  fof(f24,plain,(
% 1.30/0.54    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.30/0.55    inference(cnf_transformation,[],[f17])).
% 1.30/0.55  % SZS output end Proof for theBenchmark
% 1.30/0.55  % (32257)------------------------------
% 1.30/0.55  % (32257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (32257)Termination reason: Refutation
% 1.30/0.55  
% 1.30/0.55  % (32257)Memory used [KB]: 6268
% 1.30/0.55  % (32257)Time elapsed: 0.129 s
% 1.30/0.55  % (32257)------------------------------
% 1.30/0.55  % (32257)------------------------------
% 1.30/0.55  % (32252)Success in time 0.177 s
%------------------------------------------------------------------------------
