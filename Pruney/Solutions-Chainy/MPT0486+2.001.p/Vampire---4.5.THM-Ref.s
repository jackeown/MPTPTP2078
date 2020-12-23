%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:18 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 125 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  170 ( 250 expanded)
%              Number of equality atoms :   81 ( 148 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f202,f381])).

fof(f381,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | spl12_1 ),
    inference(subsumption_resolution,[],[f379,f358])).

fof(f358,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f353,f95])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f56,f58,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f353,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f156,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f135,f105,f154])).

fof(f154,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f92,f151])).

fof(f151,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f109,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f139,f149])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f143,f148])).

fof(f148,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f144,f147])).

fof(f147,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f145,f146])).

fof(f146,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f145,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f144,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f143,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f139,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f109,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f105,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f156,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(definition_unfolding,[],[f87,f105])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f379,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f201,f353,f353,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK7(X0,X1),X0)
      | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK7(X0,X1) != sK8(X0,X1)
              | ~ r2_hidden(sK7(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
            & ( ( sK7(X0,X1) = sK8(X0,X1)
                & r2_hidden(sK7(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f71,f72])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK7(X0,X1) != sK8(X0,X1)
          | ~ r2_hidden(sK7(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
        & ( ( sK7(X0,X1) = sK8(X0,X1)
            & r2_hidden(sK7(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f38])).

% (32728)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (32722)Refutation not found, incomplete strategy% (32722)------------------------------
% (32722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32722)Termination reason: Refutation not found, incomplete strategy

% (32722)Memory used [KB]: 1791
% (32722)Time elapsed: 0.147 s
% (32722)------------------------------
% (32722)------------------------------
% (32720)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f38,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f201,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl12_1
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f202,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f85,f199])).

fof(f85,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f41])).

fof(f41,negated_conjecture,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f40])).

fof(f40,conjecture,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:17:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (32712)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.49  % (32729)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.49  % (32729)Refutation not found, incomplete strategy% (32729)------------------------------
% 0.21/0.49  % (32729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32729)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32729)Memory used [KB]: 10746
% 0.21/0.49  % (32729)Time elapsed: 0.073 s
% 0.21/0.49  % (32729)------------------------------
% 0.21/0.49  % (32729)------------------------------
% 0.21/0.52  % (32717)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (32709)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (32716)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.27/0.53  % (32733)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.53  % (32722)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.54  % (32705)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.54  % (32705)Refutation not found, incomplete strategy% (32705)------------------------------
% 1.27/0.54  % (32705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (32705)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (32705)Memory used [KB]: 1663
% 1.27/0.54  % (32705)Time elapsed: 0.113 s
% 1.27/0.54  % (32705)------------------------------
% 1.27/0.54  % (32705)------------------------------
% 1.27/0.54  % (32711)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.27/0.54  % (32706)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.54  % (32725)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.27/0.54  % (32727)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.54  % (32708)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.27/0.54  % (32704)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.54  % (32734)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.27/0.55  % (32707)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.27/0.55  % (32734)Refutation not found, incomplete strategy% (32734)------------------------------
% 1.27/0.55  % (32734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (32734)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (32734)Memory used [KB]: 1663
% 1.27/0.55  % (32734)Time elapsed: 0.126 s
% 1.27/0.55  % (32734)------------------------------
% 1.27/0.55  % (32734)------------------------------
% 1.27/0.55  % (32731)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.55  % (32731)Refutation not found, incomplete strategy% (32731)------------------------------
% 1.43/0.55  % (32731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (32731)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (32731)Memory used [KB]: 6268
% 1.43/0.55  % (32731)Time elapsed: 0.126 s
% 1.43/0.55  % (32731)------------------------------
% 1.43/0.55  % (32731)------------------------------
% 1.43/0.55  % (32710)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.55  % (32713)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.55  % (32721)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.55  % (32723)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.55  % (32721)Refutation not found, incomplete strategy% (32721)------------------------------
% 1.43/0.55  % (32721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (32721)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (32721)Memory used [KB]: 10746
% 1.43/0.55  % (32721)Time elapsed: 0.137 s
% 1.43/0.55  % (32721)------------------------------
% 1.43/0.55  % (32721)------------------------------
% 1.43/0.55  % (32723)Refutation not found, incomplete strategy% (32723)------------------------------
% 1.43/0.55  % (32723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (32723)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (32723)Memory used [KB]: 1791
% 1.43/0.55  % (32723)Time elapsed: 0.137 s
% 1.43/0.55  % (32723)------------------------------
% 1.43/0.55  % (32723)------------------------------
% 1.43/0.55  % (32726)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.55  % (32719)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.43/0.56  % (32715)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.43/0.56  % (32719)Refutation not found, incomplete strategy% (32719)------------------------------
% 1.43/0.56  % (32719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (32719)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (32719)Memory used [KB]: 1791
% 1.43/0.56  % (32719)Time elapsed: 0.107 s
% 1.43/0.56  % (32719)------------------------------
% 1.43/0.56  % (32719)------------------------------
% 1.43/0.56  % (32733)Refutation not found, incomplete strategy% (32733)------------------------------
% 1.43/0.56  % (32733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (32733)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (32733)Memory used [KB]: 10746
% 1.43/0.56  % (32733)Time elapsed: 0.142 s
% 1.43/0.56  % (32733)------------------------------
% 1.43/0.56  % (32733)------------------------------
% 1.43/0.56  % (32732)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.56  % (32715)Refutation not found, incomplete strategy% (32715)------------------------------
% 1.43/0.56  % (32715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (32715)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (32715)Memory used [KB]: 10746
% 1.43/0.56  % (32715)Time elapsed: 0.140 s
% 1.43/0.56  % (32715)------------------------------
% 1.43/0.56  % (32715)------------------------------
% 1.43/0.56  % (32732)Refutation not found, incomplete strategy% (32732)------------------------------
% 1.43/0.56  % (32732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (32732)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (32732)Memory used [KB]: 6268
% 1.43/0.56  % (32732)Time elapsed: 0.139 s
% 1.43/0.56  % (32732)------------------------------
% 1.43/0.56  % (32732)------------------------------
% 1.43/0.56  % (32724)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.56  % (32718)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.43/0.56  % (32730)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.43/0.56  % (32725)Refutation found. Thanks to Tanya!
% 1.43/0.56  % SZS status Theorem for theBenchmark
% 1.43/0.56  % SZS output start Proof for theBenchmark
% 1.43/0.56  fof(f382,plain,(
% 1.43/0.56    $false),
% 1.43/0.56    inference(avatar_sat_refutation,[],[f202,f381])).
% 1.43/0.56  fof(f381,plain,(
% 1.43/0.56    spl12_1),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f380])).
% 1.43/0.56  fof(f380,plain,(
% 1.43/0.56    $false | spl12_1),
% 1.43/0.56    inference(subsumption_resolution,[],[f379,f358])).
% 1.43/0.56  fof(f358,plain,(
% 1.43/0.56    v1_relat_1(k1_xboole_0)),
% 1.43/0.56    inference(unit_resulting_resolution,[],[f353,f95])).
% 1.43/0.56  fof(f95,plain,(
% 1.43/0.56    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f59])).
% 1.43/0.56  fof(f59,plain,(
% 1.43/0.56    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0))) & (! [X4] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f56,f58,f57])).
% 1.43/0.56  fof(f57,plain,(
% 1.43/0.56    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f58,plain,(
% 1.43/0.56    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK1(X4),sK2(X4)) = X4)),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f56,plain,(
% 1.43/0.56    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.43/0.56    inference(rectify,[],[f55])).
% 1.43/0.56  fof(f55,plain,(
% 1.43/0.56    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.43/0.56    inference(nnf_transformation,[],[f45])).
% 1.43/0.56  fof(f45,plain,(
% 1.43/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f39])).
% 1.43/0.56  fof(f39,axiom,(
% 1.43/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.43/0.56  fof(f353,plain,(
% 1.43/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.43/0.56    inference(unit_resulting_resolution,[],[f156,f178])).
% 1.43/0.56  fof(f178,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k6_subset_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f135,f105,f154])).
% 1.43/0.56  fof(f154,plain,(
% 1.43/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f92,f151])).
% 1.43/0.56  fof(f151,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f109,f150])).
% 1.43/0.56  fof(f150,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f139,f149])).
% 1.43/0.56  fof(f149,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f143,f148])).
% 1.43/0.56  fof(f148,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f144,f147])).
% 1.43/0.56  fof(f147,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f145,f146])).
% 1.43/0.56  fof(f146,plain,(
% 1.43/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f21])).
% 1.43/0.56  fof(f21,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.43/0.56  fof(f145,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f20])).
% 1.43/0.56  fof(f20,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.43/0.56  fof(f144,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f19])).
% 1.43/0.56  fof(f19,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.43/0.56  fof(f143,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f18])).
% 1.43/0.56  fof(f18,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.43/0.56  fof(f139,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f17])).
% 1.43/0.56  fof(f17,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.43/0.56  fof(f109,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f16])).
% 1.43/0.56  fof(f16,axiom,(
% 1.43/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.43/0.56  fof(f92,plain,(
% 1.43/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f15])).
% 1.43/0.56  fof(f15,axiom,(
% 1.43/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.43/0.56  fof(f105,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f35])).
% 1.43/0.56  fof(f35,axiom,(
% 1.43/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.43/0.56  fof(f135,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f83])).
% 1.43/0.56  fof(f83,plain,(
% 1.43/0.56    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.43/0.56    inference(nnf_transformation,[],[f31])).
% 1.43/0.56  fof(f31,axiom,(
% 1.43/0.56    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.43/0.56  fof(f156,plain,(
% 1.43/0.56    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f87,f105])).
% 1.43/0.56  fof(f87,plain,(
% 1.43/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f10])).
% 1.43/0.56  fof(f10,axiom,(
% 1.43/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.43/0.56  fof(f379,plain,(
% 1.43/0.56    ~v1_relat_1(k1_xboole_0) | spl12_1),
% 1.43/0.56    inference(unit_resulting_resolution,[],[f201,f353,f353,f116])).
% 1.43/0.56  fof(f116,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(sK7(X0,X1),X0) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) | k6_relat_1(X0) = X1) )),
% 1.43/0.56    inference(cnf_transformation,[],[f73])).
% 1.43/0.56  fof(f73,plain,(
% 1.43/0.56    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK7(X0,X1) != sK8(X0,X1) | ~r2_hidden(sK7(X0,X1),X0) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)) & ((sK7(X0,X1) = sK8(X0,X1) & r2_hidden(sK7(X0,X1),X0)) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f71,f72])).
% 1.43/0.56  fof(f72,plain,(
% 1.43/0.56    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK7(X0,X1) != sK8(X0,X1) | ~r2_hidden(sK7(X0,X1),X0) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)) & ((sK7(X0,X1) = sK8(X0,X1) & r2_hidden(sK7(X0,X1),X0)) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1))))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f71,plain,(
% 1.43/0.56    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(rectify,[],[f70])).
% 1.43/0.56  fof(f70,plain,(
% 1.43/0.56    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(flattening,[],[f69])).
% 1.43/0.56  fof(f69,plain,(
% 1.43/0.56    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(nnf_transformation,[],[f47])).
% 1.43/0.56  fof(f47,plain,(
% 1.43/0.56    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f38])).
% 1.43/0.57  % (32728)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.57  % (32722)Refutation not found, incomplete strategy% (32722)------------------------------
% 1.43/0.57  % (32722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (32722)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (32722)Memory used [KB]: 1791
% 1.43/0.57  % (32722)Time elapsed: 0.147 s
% 1.43/0.57  % (32722)------------------------------
% 1.43/0.57  % (32722)------------------------------
% 1.43/0.57  % (32720)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.58  fof(f38,axiom,(
% 1.43/0.58    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).
% 1.43/0.58  fof(f201,plain,(
% 1.43/0.58    k1_xboole_0 != k6_relat_1(k1_xboole_0) | spl12_1),
% 1.43/0.58    inference(avatar_component_clause,[],[f199])).
% 1.43/0.58  fof(f199,plain,(
% 1.43/0.58    spl12_1 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.43/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.43/0.58  fof(f202,plain,(
% 1.43/0.58    ~spl12_1),
% 1.43/0.58    inference(avatar_split_clause,[],[f85,f199])).
% 1.43/0.58  fof(f85,plain,(
% 1.43/0.58    k1_xboole_0 != k6_relat_1(k1_xboole_0)),
% 1.43/0.58    inference(cnf_transformation,[],[f42])).
% 1.43/0.58  fof(f42,plain,(
% 1.43/0.58    k1_xboole_0 != k6_relat_1(k1_xboole_0)),
% 1.43/0.58    inference(flattening,[],[f41])).
% 1.43/0.58  fof(f41,negated_conjecture,(
% 1.43/0.58    ~k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.43/0.58    inference(negated_conjecture,[],[f40])).
% 1.43/0.58  fof(f40,conjecture,(
% 1.43/0.58    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.43/0.58  % SZS output end Proof for theBenchmark
% 1.43/0.58  % (32725)------------------------------
% 1.43/0.58  % (32725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.58  % (32725)Termination reason: Refutation
% 1.43/0.58  
% 1.43/0.58  % (32725)Memory used [KB]: 11001
% 1.43/0.58  % (32725)Time elapsed: 0.150 s
% 1.43/0.58  % (32725)------------------------------
% 1.43/0.58  % (32725)------------------------------
% 1.43/0.58  % (32703)Success in time 0.212 s
%------------------------------------------------------------------------------
