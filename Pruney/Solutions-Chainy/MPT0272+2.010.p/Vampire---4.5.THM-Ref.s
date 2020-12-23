%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:13 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 179 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  167 ( 321 expanded)
%              Number of equality atoms :   55 ( 156 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1397,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f71,f76,f143,f1367,f1396])).

fof(f1396,plain,(
    ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f1376])).

fof(f1376,plain,
    ( $false
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f78,f84,f1366,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1366,plain,
    ( ! [X1] : ~ r2_hidden(sK0,X1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f1365])).

fof(f1365,plain,
    ( spl2_7
  <=> ! [X1] : ~ r2_hidden(sK0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f84,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(condensation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f35,f33])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(resolution,[],[f54,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f1367,plain,
    ( spl2_4
    | spl2_7
    | spl2_3 ),
    inference(avatar_split_clause,[],[f1363,f73,f1365,f140])).

fof(f140,plain,
    ( spl2_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f73,plain,
    ( spl2_3
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1363,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r2_hidden(sK0,sK1) )
    | spl2_3 ),
    inference(duplicate_literal_removal,[],[f1361])).

fof(f1361,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r2_hidden(sK0,sK1)
        | ~ r2_hidden(sK0,X1) )
    | spl2_3 ),
    inference(resolution,[],[f1358,f36])).

fof(f1358,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK0,k5_xboole_0(X2,sK1))
        | ~ r2_hidden(sK0,X2) )
    | spl2_3 ),
    inference(trivial_inequality_removal,[],[f1355])).

fof(f1355,plain,
    ( ! [X2] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
        | ~ r2_hidden(sK0,X2)
        | ~ r2_hidden(sK0,k5_xboole_0(X2,sK1)) )
    | spl2_3 ),
    inference(superposition,[],[f1295,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f49,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f1295,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k5_xboole_0(X0,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(sK0,X0) )
    | spl2_3 ),
    inference(superposition,[],[f75,f130])).

fof(f130,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(k5_xboole_0(X3,X5),k2_enumset1(X4,X4,X4,X4)) = k5_xboole_0(k2_enumset1(X4,X4,X4,X4),k3_xboole_0(X5,k2_enumset1(X4,X4,X4,X4)))
      | ~ r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f38,f52])).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f75,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f143,plain,
    ( ~ spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f138,f67,f140])).

fof(f67,plain,
    ( spl2_2
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f138,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK0,sK1)
    | spl2_2 ),
    inference(forward_demodulation,[],[f135,f33])).

fof(f135,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,sK1)
    | spl2_2 ),
    inference(superposition,[],[f69,f52])).

fof(f69,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f76,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f65,f73])).

fof(f65,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f50,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f29,f49,f30,f49])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f71,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f64,f59,f67])).

fof(f59,plain,
    ( spl2_1
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f64,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_1 ),
    inference(superposition,[],[f61,f39])).

fof(f61,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f62,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f51,f59])).

fof(f51,plain,(
    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f28,f30,f49])).

fof(f28,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (15194)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.50  % (15196)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (15187)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (15195)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (15187)Refutation not found, incomplete strategy% (15187)------------------------------
% 0.21/0.51  % (15187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15187)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15187)Memory used [KB]: 1663
% 0.21/0.51  % (15187)Time elapsed: 0.054 s
% 0.21/0.51  % (15187)------------------------------
% 0.21/0.51  % (15187)------------------------------
% 0.21/0.51  % (15186)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (15179)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (15178)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (15176)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.19/0.52  % (15202)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.19/0.53  % (15193)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.19/0.53  % (15177)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.19/0.53  % (15185)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.19/0.53  % (15183)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.19/0.53  % (15185)Refutation not found, incomplete strategy% (15185)------------------------------
% 1.19/0.53  % (15185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (15185)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.53  
% 1.19/0.53  % (15185)Memory used [KB]: 10618
% 1.19/0.53  % (15185)Time elapsed: 0.133 s
% 1.19/0.53  % (15185)------------------------------
% 1.19/0.53  % (15185)------------------------------
% 1.30/0.54  % (15197)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.54  % (15201)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.54  % (15199)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.30/0.54  % (15197)Refutation not found, incomplete strategy% (15197)------------------------------
% 1.30/0.54  % (15197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (15197)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (15197)Memory used [KB]: 10618
% 1.30/0.54  % (15197)Time elapsed: 0.136 s
% 1.30/0.54  % (15197)------------------------------
% 1.30/0.54  % (15197)------------------------------
% 1.30/0.54  % (15199)Refutation not found, incomplete strategy% (15199)------------------------------
% 1.30/0.54  % (15199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (15199)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (15199)Memory used [KB]: 6140
% 1.30/0.54  % (15199)Time elapsed: 0.135 s
% 1.30/0.54  % (15199)------------------------------
% 1.30/0.54  % (15199)------------------------------
% 1.30/0.54  % (15201)Refutation not found, incomplete strategy% (15201)------------------------------
% 1.30/0.54  % (15201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (15201)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (15201)Memory used [KB]: 10618
% 1.30/0.54  % (15201)Time elapsed: 0.136 s
% 1.30/0.54  % (15201)------------------------------
% 1.30/0.54  % (15201)------------------------------
% 1.30/0.54  % (15202)Refutation not found, incomplete strategy% (15202)------------------------------
% 1.30/0.54  % (15202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (15175)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.54  % (15173)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.54  % (15200)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.54  % (15191)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.54  % (15191)Refutation not found, incomplete strategy% (15191)------------------------------
% 1.30/0.54  % (15191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (15200)Refutation not found, incomplete strategy% (15200)------------------------------
% 1.30/0.54  % (15200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (15183)Refutation not found, incomplete strategy% (15183)------------------------------
% 1.30/0.55  % (15183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (15191)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (15191)Memory used [KB]: 1663
% 1.30/0.55  % (15191)Time elapsed: 0.142 s
% 1.30/0.55  % (15191)------------------------------
% 1.30/0.55  % (15191)------------------------------
% 1.30/0.55  % (15200)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (15200)Memory used [KB]: 6140
% 1.30/0.55  % (15200)Time elapsed: 0.140 s
% 1.30/0.55  % (15200)------------------------------
% 1.30/0.55  % (15200)------------------------------
% 1.30/0.55  % (15190)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.55  % (15192)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.55  % (15183)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (15183)Memory used [KB]: 10618
% 1.30/0.55  % (15183)Time elapsed: 0.144 s
% 1.30/0.55  % (15183)------------------------------
% 1.30/0.55  % (15183)------------------------------
% 1.30/0.55  % (15202)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (15202)Memory used [KB]: 1663
% 1.30/0.55  % (15202)Time elapsed: 0.004 s
% 1.30/0.55  % (15202)------------------------------
% 1.30/0.55  % (15202)------------------------------
% 1.30/0.55  % (15174)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.55  % (15188)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.30/0.55  % (15180)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.30/0.55  % (15181)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.30/0.56  % (15184)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.56  % (15182)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.56  % (15184)Refutation not found, incomplete strategy% (15184)------------------------------
% 1.30/0.56  % (15184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (15184)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (15184)Memory used [KB]: 6140
% 1.30/0.56  % (15184)Time elapsed: 0.148 s
% 1.30/0.56  % (15184)------------------------------
% 1.30/0.56  % (15184)------------------------------
% 1.30/0.56  % (15198)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.56  % (15174)Refutation not found, incomplete strategy% (15174)------------------------------
% 1.30/0.56  % (15174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (15174)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (15174)Memory used [KB]: 1663
% 1.30/0.56  % (15174)Time elapsed: 0.143 s
% 1.30/0.56  % (15174)------------------------------
% 1.30/0.56  % (15174)------------------------------
% 1.30/0.56  % (15198)Refutation not found, incomplete strategy% (15198)------------------------------
% 1.30/0.56  % (15198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (15189)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.56  % (15190)Refutation not found, incomplete strategy% (15190)------------------------------
% 1.30/0.56  % (15190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (15190)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (15190)Memory used [KB]: 1663
% 1.30/0.56  % (15190)Time elapsed: 0.157 s
% 1.30/0.56  % (15190)------------------------------
% 1.30/0.56  % (15190)------------------------------
% 1.30/0.57  % (15198)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.57  
% 1.30/0.57  % (15198)Memory used [KB]: 6140
% 1.30/0.57  % (15198)Time elapsed: 0.158 s
% 1.30/0.57  % (15198)------------------------------
% 1.30/0.57  % (15198)------------------------------
% 1.30/0.57  % (15189)Refutation not found, incomplete strategy% (15189)------------------------------
% 1.30/0.57  % (15189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.57  % (15189)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.57  
% 1.30/0.57  % (15189)Memory used [KB]: 10618
% 1.30/0.57  % (15189)Time elapsed: 0.156 s
% 1.30/0.57  % (15189)------------------------------
% 1.30/0.57  % (15189)------------------------------
% 1.30/0.58  % (15196)Refutation found. Thanks to Tanya!
% 1.30/0.58  % SZS status Theorem for theBenchmark
% 1.30/0.59  % SZS output start Proof for theBenchmark
% 1.30/0.59  fof(f1397,plain,(
% 1.30/0.59    $false),
% 1.30/0.59    inference(avatar_sat_refutation,[],[f62,f71,f76,f143,f1367,f1396])).
% 1.30/0.59  fof(f1396,plain,(
% 1.30/0.59    ~spl2_7),
% 1.30/0.59    inference(avatar_contradiction_clause,[],[f1376])).
% 1.30/0.59  fof(f1376,plain,(
% 1.30/0.59    $false | ~spl2_7),
% 1.30/0.59    inference(unit_resulting_resolution,[],[f78,f84,f1366,f36])).
% 1.30/0.59  fof(f36,plain,(
% 1.30/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.30/0.59    inference(cnf_transformation,[],[f23])).
% 1.30/0.59  fof(f23,plain,(
% 1.30/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.30/0.59    inference(nnf_transformation,[],[f20])).
% 1.30/0.59  fof(f20,plain,(
% 1.30/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.30/0.59    inference(ennf_transformation,[],[f2])).
% 1.30/0.59  fof(f2,axiom,(
% 1.30/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.30/0.59  fof(f1366,plain,(
% 1.30/0.59    ( ! [X1] : (~r2_hidden(sK0,X1)) ) | ~spl2_7),
% 1.30/0.59    inference(avatar_component_clause,[],[f1365])).
% 1.30/0.59  fof(f1365,plain,(
% 1.30/0.59    spl2_7 <=> ! [X1] : ~r2_hidden(sK0,X1)),
% 1.30/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.30/0.59  fof(f84,plain,(
% 1.30/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.30/0.59    inference(condensation,[],[f83])).
% 1.30/0.59  fof(f83,plain,(
% 1.30/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 1.30/0.59    inference(duplicate_literal_removal,[],[f82])).
% 1.30/0.59  fof(f82,plain,(
% 1.30/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.30/0.59    inference(superposition,[],[f35,f33])).
% 1.30/0.59  fof(f33,plain,(
% 1.30/0.59    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.30/0.59    inference(cnf_transformation,[],[f6])).
% 1.30/0.59  fof(f6,axiom,(
% 1.30/0.59    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.30/0.59  fof(f35,plain,(
% 1.30/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.30/0.59    inference(cnf_transformation,[],[f23])).
% 1.30/0.59  fof(f78,plain,(
% 1.30/0.59    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))) )),
% 1.30/0.59    inference(resolution,[],[f54,f56])).
% 1.30/0.59  fof(f56,plain,(
% 1.30/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.30/0.59    inference(equality_resolution,[],[f45])).
% 1.30/0.59  fof(f45,plain,(
% 1.30/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.30/0.59    inference(cnf_transformation,[],[f27])).
% 1.30/0.59  fof(f27,plain,(
% 1.30/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.59    inference(flattening,[],[f26])).
% 1.30/0.59  fof(f26,plain,(
% 1.30/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.59    inference(nnf_transformation,[],[f3])).
% 1.30/0.59  fof(f3,axiom,(
% 1.30/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.30/0.59  fof(f54,plain,(
% 1.30/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.30/0.59    inference(definition_unfolding,[],[f41,f48])).
% 1.30/0.59  fof(f48,plain,(
% 1.30/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.30/0.59    inference(definition_unfolding,[],[f43,f47])).
% 1.30/0.59  fof(f47,plain,(
% 1.30/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.30/0.59    inference(cnf_transformation,[],[f9])).
% 1.30/0.59  fof(f9,axiom,(
% 1.30/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.30/0.59  fof(f43,plain,(
% 1.30/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.30/0.59    inference(cnf_transformation,[],[f8])).
% 1.30/0.59  fof(f8,axiom,(
% 1.30/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.59  fof(f41,plain,(
% 1.30/0.59    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.30/0.59    inference(cnf_transformation,[],[f25])).
% 1.30/0.59  fof(f25,plain,(
% 1.30/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.30/0.59    inference(flattening,[],[f24])).
% 1.30/0.59  fof(f24,plain,(
% 1.30/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.30/0.59    inference(nnf_transformation,[],[f15])).
% 1.30/0.59  fof(f15,axiom,(
% 1.30/0.59    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.30/0.59  fof(f1367,plain,(
% 1.30/0.59    spl2_4 | spl2_7 | spl2_3),
% 1.30/0.59    inference(avatar_split_clause,[],[f1363,f73,f1365,f140])).
% 1.30/0.59  fof(f140,plain,(
% 1.30/0.59    spl2_4 <=> r2_hidden(sK0,sK1)),
% 1.30/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.30/0.59  fof(f73,plain,(
% 1.30/0.59    spl2_3 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.30/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.30/0.59  fof(f1363,plain,(
% 1.30/0.59    ( ! [X1] : (~r2_hidden(sK0,X1) | r2_hidden(sK0,sK1)) ) | spl2_3),
% 1.30/0.59    inference(duplicate_literal_removal,[],[f1361])).
% 1.30/0.59  fof(f1361,plain,(
% 1.30/0.59    ( ! [X1] : (~r2_hidden(sK0,X1) | r2_hidden(sK0,sK1) | ~r2_hidden(sK0,X1)) ) | spl2_3),
% 1.30/0.59    inference(resolution,[],[f1358,f36])).
% 1.30/0.59  fof(f1358,plain,(
% 1.30/0.59    ( ! [X2] : (~r2_hidden(sK0,k5_xboole_0(X2,sK1)) | ~r2_hidden(sK0,X2)) ) | spl2_3),
% 1.30/0.59    inference(trivial_inequality_removal,[],[f1355])).
% 1.30/0.59  fof(f1355,plain,(
% 1.30/0.59    ( ! [X2] : (k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,X2) | ~r2_hidden(sK0,k5_xboole_0(X2,sK1))) ) | spl2_3),
% 1.30/0.59    inference(superposition,[],[f1295,f52])).
% 1.30/0.59  fof(f52,plain,(
% 1.30/0.59    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 1.30/0.59    inference(definition_unfolding,[],[f31,f49,f49])).
% 1.30/0.59  fof(f49,plain,(
% 1.30/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.30/0.59    inference(definition_unfolding,[],[f32,f48])).
% 1.30/0.59  fof(f32,plain,(
% 1.30/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.30/0.59    inference(cnf_transformation,[],[f7])).
% 1.30/0.59  fof(f7,axiom,(
% 1.30/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.30/0.59  fof(f31,plain,(
% 1.30/0.59    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 1.30/0.59    inference(cnf_transformation,[],[f19])).
% 1.30/0.59  fof(f19,plain,(
% 1.30/0.59    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.30/0.59    inference(ennf_transformation,[],[f14])).
% 1.30/0.59  fof(f14,axiom,(
% 1.30/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.30/0.59  fof(f1295,plain,(
% 1.30/0.59    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k5_xboole_0(X0,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,X0)) ) | spl2_3),
% 1.30/0.59    inference(superposition,[],[f75,f130])).
% 1.30/0.59  fof(f130,plain,(
% 1.30/0.59    ( ! [X4,X5,X3] : (k3_xboole_0(k5_xboole_0(X3,X5),k2_enumset1(X4,X4,X4,X4)) = k5_xboole_0(k2_enumset1(X4,X4,X4,X4),k3_xboole_0(X5,k2_enumset1(X4,X4,X4,X4))) | ~r2_hidden(X4,X3)) )),
% 1.30/0.59    inference(superposition,[],[f38,f52])).
% 1.30/0.59  fof(f38,plain,(
% 1.30/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.30/0.59    inference(cnf_transformation,[],[f5])).
% 1.30/0.59  fof(f5,axiom,(
% 1.30/0.59    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.30/0.59  fof(f75,plain,(
% 1.30/0.59    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_3),
% 1.30/0.59    inference(avatar_component_clause,[],[f73])).
% 1.30/0.59  fof(f143,plain,(
% 1.30/0.59    ~spl2_4 | spl2_2),
% 1.30/0.59    inference(avatar_split_clause,[],[f138,f67,f140])).
% 1.30/0.59  fof(f67,plain,(
% 1.30/0.59    spl2_2 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.30/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.30/0.59  fof(f138,plain,(
% 1.30/0.59    ~r2_hidden(sK0,sK1) | spl2_2),
% 1.30/0.59    inference(trivial_inequality_removal,[],[f137])).
% 1.30/0.59  fof(f137,plain,(
% 1.30/0.59    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,sK1) | spl2_2),
% 1.30/0.59    inference(forward_demodulation,[],[f135,f33])).
% 1.30/0.59  fof(f135,plain,(
% 1.30/0.59    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,sK1) | spl2_2),
% 1.30/0.59    inference(superposition,[],[f69,f52])).
% 1.30/0.59  fof(f69,plain,(
% 1.30/0.59    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_2),
% 1.30/0.59    inference(avatar_component_clause,[],[f67])).
% 1.30/0.59  fof(f76,plain,(
% 1.30/0.59    ~spl2_3),
% 1.30/0.59    inference(avatar_split_clause,[],[f65,f73])).
% 1.30/0.59  fof(f65,plain,(
% 1.30/0.59    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.30/0.59    inference(forward_demodulation,[],[f50,f39])).
% 1.30/0.59  fof(f39,plain,(
% 1.30/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.30/0.59    inference(cnf_transformation,[],[f1])).
% 1.30/0.59  fof(f1,axiom,(
% 1.30/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.30/0.59  fof(f50,plain,(
% 1.30/0.59    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.30/0.59    inference(definition_unfolding,[],[f29,f49,f30,f49])).
% 1.30/0.59  fof(f30,plain,(
% 1.30/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.30/0.59    inference(cnf_transformation,[],[f4])).
% 1.30/0.59  fof(f4,axiom,(
% 1.30/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.30/0.59  fof(f29,plain,(
% 1.30/0.59    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.30/0.59    inference(cnf_transformation,[],[f22])).
% 1.30/0.59  fof(f22,plain,(
% 1.30/0.59    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.30/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21])).
% 1.30/0.59  fof(f21,plain,(
% 1.30/0.59    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.30/0.59    introduced(choice_axiom,[])).
% 1.30/0.59  fof(f18,plain,(
% 1.30/0.59    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 1.30/0.59    inference(ennf_transformation,[],[f17])).
% 1.30/0.59  fof(f17,negated_conjecture,(
% 1.30/0.59    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 1.30/0.59    inference(negated_conjecture,[],[f16])).
% 1.30/0.59  fof(f16,conjecture,(
% 1.30/0.59    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 1.30/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 1.30/0.59  fof(f71,plain,(
% 1.30/0.59    ~spl2_2 | spl2_1),
% 1.30/0.59    inference(avatar_split_clause,[],[f64,f59,f67])).
% 1.30/0.59  fof(f59,plain,(
% 1.30/0.59    spl2_1 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.30/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.30/0.59  fof(f64,plain,(
% 1.30/0.59    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_1),
% 1.30/0.59    inference(superposition,[],[f61,f39])).
% 1.30/0.59  fof(f61,plain,(
% 1.30/0.59    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl2_1),
% 1.30/0.59    inference(avatar_component_clause,[],[f59])).
% 1.30/0.59  fof(f62,plain,(
% 1.30/0.59    ~spl2_1),
% 1.30/0.59    inference(avatar_split_clause,[],[f51,f59])).
% 1.30/0.59  fof(f51,plain,(
% 1.30/0.59    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.30/0.59    inference(definition_unfolding,[],[f28,f30,f49])).
% 1.30/0.59  fof(f28,plain,(
% 1.30/0.59    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.30/0.59    inference(cnf_transformation,[],[f22])).
% 1.30/0.59  % SZS output end Proof for theBenchmark
% 1.30/0.59  % (15196)------------------------------
% 1.30/0.59  % (15196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.59  % (15196)Termination reason: Refutation
% 1.30/0.59  
% 1.30/0.59  % (15196)Memory used [KB]: 11769
% 1.30/0.59  % (15196)Time elapsed: 0.137 s
% 1.30/0.59  % (15196)------------------------------
% 1.30/0.59  % (15196)------------------------------
% 1.30/0.59  % (15171)Success in time 0.225 s
%------------------------------------------------------------------------------
