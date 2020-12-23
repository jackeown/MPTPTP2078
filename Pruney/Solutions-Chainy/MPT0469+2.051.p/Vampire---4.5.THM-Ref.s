%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 102 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  202 ( 288 expanded)
%              Number of equality atoms :   32 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f90,f113,f114,f217,f224])).

fof(f224,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl7_6 ),
    inference(resolution,[],[f221,f38])).

fof(f38,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f221,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | spl7_6 ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | spl7_6 ),
    inference(superposition,[],[f170,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f170,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl7_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

% (18096)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f217,plain,
    ( spl7_2
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f212,f50])).

fof(f50,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl7_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f212,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_6 ),
    inference(resolution,[],[f203,f35])).

fof(f203,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(resolution,[],[f183,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK6(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f183,plain,
    ( ! [X1] : ~ r2_hidden(X1,k2_relat_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(resolution,[],[f179,f40])).

fof(f40,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f179,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_6 ),
    inference(resolution,[],[f171,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f171,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f114,plain,
    ( spl7_5
    | spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f91,f65,f44,f76])).

fof(f76,plain,
    ( spl7_5
  <=> r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f44,plain,
    ( spl7_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

% (18106)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f65,plain,
    ( spl7_3
  <=> r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f91,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | spl7_3 ),
    inference(resolution,[],[f67,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f20,f19,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f67,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f113,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl7_5 ),
    inference(resolution,[],[f105,f38])).

fof(f105,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f104,f36])).

fof(f104,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(X0,X0),sK4(X0,X0)),X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_5 ),
    inference(superposition,[],[f78,f35])).

fof(f78,plain,
    ( r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f90,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl7_3 ),
    inference(resolution,[],[f84,f38])).

fof(f84,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f82,f36])).

fof(f82,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,X0),X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_3 ),
    inference(superposition,[],[f66,f35])).

fof(f66,plain,
    ( r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f51,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f26,f48,f44])).

fof(f26,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (18101)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.41  % (18101)Refutation not found, incomplete strategy% (18101)------------------------------
% 0.21/0.41  % (18101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (18101)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.41  
% 0.21/0.41  % (18101)Memory used [KB]: 6140
% 0.21/0.41  % (18101)Time elapsed: 0.003 s
% 0.21/0.41  % (18101)------------------------------
% 0.21/0.41  % (18101)------------------------------
% 0.21/0.45  % (18087)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.45  % (18087)Refutation not found, incomplete strategy% (18087)------------------------------
% 0.21/0.45  % (18087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (18087)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (18087)Memory used [KB]: 10490
% 0.21/0.45  % (18087)Time elapsed: 0.033 s
% 0.21/0.45  % (18087)------------------------------
% 0.21/0.45  % (18087)------------------------------
% 0.21/0.46  % (18086)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (18086)Refutation not found, incomplete strategy% (18086)------------------------------
% 0.21/0.46  % (18086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (18086)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (18086)Memory used [KB]: 6140
% 0.21/0.46  % (18086)Time elapsed: 0.051 s
% 0.21/0.46  % (18086)------------------------------
% 0.21/0.46  % (18086)------------------------------
% 0.21/0.48  % (18088)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (18094)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (18089)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (18105)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (18095)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (18105)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f51,f90,f113,f114,f217,f224])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    spl7_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f223])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    $false | spl7_6),
% 0.21/0.49    inference(resolution,[],[f221,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0)) ) | spl7_6),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f220])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_xboole_0(X0)) ) | spl7_6),
% 0.21/0.49    inference(superposition,[],[f170,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0) | spl7_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f169])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    spl7_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.49  % (18096)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    spl7_2 | ~spl7_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f216])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    $false | (spl7_2 | ~spl7_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f212,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl7_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl7_6),
% 0.21/0.49    inference(resolution,[],[f203,f35])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl7_6),
% 0.21/0.49    inference(resolution,[],[f183,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(rectify,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(k1_xboole_0))) ) | ~spl7_6),
% 0.21/0.49    inference(resolution,[],[f179,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0) => r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.49    inference(rectify,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_6),
% 0.21/0.49    inference(resolution,[],[f171,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl7_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f169])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl7_5 | spl7_1 | spl7_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f91,f65,f44,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl7_5 <=> r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    spl7_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  % (18106)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl7_3 <=> r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | spl7_3),
% 0.21/0.49    inference(resolution,[],[f67,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f20,f19,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(rectify,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl7_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ~spl7_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    $false | ~spl7_5),
% 0.21/0.49    inference(resolution,[],[f105,f38])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl7_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f104,f36])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0,X0),sK4(X0,X0)),X0) | ~v1_xboole_0(X0)) ) | ~spl7_5),
% 0.21/0.49    inference(superposition,[],[f78,f35])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl7_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~spl7_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    $false | ~spl7_3),
% 0.21/0.49    inference(resolution,[],[f84,f38])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl7_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f36])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(X0,X0),X0) | ~v1_xboole_0(X0)) ) | ~spl7_3),
% 0.21/0.49    inference(superposition,[],[f66,f35])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl7_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~spl7_1 | ~spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f48,f44])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18105)------------------------------
% 0.21/0.49  % (18105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18105)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18105)Memory used [KB]: 6140
% 0.21/0.49  % (18105)Time elapsed: 0.077 s
% 0.21/0.49  % (18105)------------------------------
% 0.21/0.49  % (18105)------------------------------
% 0.21/0.49  % (18106)Refutation not found, incomplete strategy% (18106)------------------------------
% 0.21/0.49  % (18106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18106)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (18106)Memory used [KB]: 10618
% 0.21/0.49  % (18106)Time elapsed: 0.085 s
% 0.21/0.49  % (18106)------------------------------
% 0.21/0.49  % (18106)------------------------------
% 0.21/0.49  % (18085)Success in time 0.137 s
%------------------------------------------------------------------------------
