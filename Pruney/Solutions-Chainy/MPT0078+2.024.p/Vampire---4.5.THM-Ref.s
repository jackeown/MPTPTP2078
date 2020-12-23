%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 197 expanded)
%              Number of leaves         :   17 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  209 ( 581 expanded)
%              Number of equality atoms :   44 ( 132 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f1672,f1993,f2183])).

% (20465)Refutation not found, incomplete strategy% (20465)------------------------------
% (20465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20465)Termination reason: Refutation not found, incomplete strategy

% (20465)Memory used [KB]: 10746
% (20465)Time elapsed: 0.128 s
% (20465)------------------------------
% (20465)------------------------------
fof(f2183,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f2182])).

fof(f2182,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f1748,f85])).

fof(f85,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

% (20460)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f1748,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(global_subsumption,[],[f1746])).

fof(f1746,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(global_subsumption,[],[f1656])).

fof(f1656,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f1643,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f1643,plain,(
    ! [X4] : r1_xboole_0(k4_xboole_0(sK2,sK0),X4) ),
    inference(subsumption_resolution,[],[f1625,f63])).

fof(f63,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

% (20461)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f30,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1625,plain,(
    ! [X4] :
      ( r1_xboole_0(k4_xboole_0(sK2,sK0),X4)
      | ~ r1_xboole_0(sK1,sK2) ) ),
    inference(resolution,[],[f192,f82])).

fof(f82,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k4_xboole_0(sK2,sK0))
      | ~ r1_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f76,f50])).

fof(f76,plain,(
    ! [X0] :
      ( r1_xboole_0(k4_xboole_0(sK2,sK0),X0)
      | ~ r1_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f74,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f74,plain,(
    r1_tarski(k4_xboole_0(sK2,sK0),sK1) ),
    inference(resolution,[],[f52,f60])).

fof(f60,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f41,f35])).

fof(f35,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f192,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_xboole_0(X6,k4_xboole_0(X6,X7))
      | r1_xboole_0(k4_xboole_0(X6,X7),X8) ) ),
    inference(superposition,[],[f79,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f57,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1993,plain,
    ( ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1992])).

fof(f1992,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1991,f38])).

fof(f38,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f1991,plain,
    ( sK0 = sK2
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1972,f132])).

fof(f132,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1972,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK2)
    | sK0 = sK2
    | ~ spl5_1 ),
    inference(superposition,[],[f51,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f1672,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f1671])).

fof(f1671,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f1645,f136])).

fof(f136,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_6
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1645,plain,(
    ! [X0] : r1_xboole_0(X0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f1642,f324])).

fof(f324,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f323])).

fof(f323,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f68,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK4(X5,X4),X3)
      | ~ r1_xboole_0(X3,X4)
      | r1_xboole_0(X5,X4) ) ),
    inference(resolution,[],[f49,f48])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1642,plain,(
    ! [X3] : r1_xboole_0(k4_xboole_0(sK0,sK2),X3) ),
    inference(subsumption_resolution,[],[f1624,f62])).

fof(f62,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f1624,plain,(
    ! [X3] :
      ( r1_xboole_0(k4_xboole_0(sK0,sK2),X3)
      | ~ r1_xboole_0(sK1,sK0) ) ),
    inference(resolution,[],[f192,f128])).

fof(f128,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k4_xboole_0(sK0,sK2))
      | ~ r1_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f126,f50])).

fof(f126,plain,(
    ! [X0] :
      ( r1_xboole_0(k4_xboole_0(sK0,sK2),X0)
      | ~ r1_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f122,f53])).

fof(f122,plain,(
    r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f75,f41])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK0,sK1))
      | r1_tarski(k4_xboole_0(X0,sK2),sK1) ) ),
    inference(superposition,[],[f52,f35])).

fof(f137,plain,
    ( spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f127,f134,f130])).

fof(f127,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f126,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (20451)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.49  % (20442)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (20451)Refutation not found, incomplete strategy% (20451)------------------------------
% 0.22/0.49  % (20451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (20451)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (20451)Memory used [KB]: 1791
% 0.22/0.49  % (20451)Time elapsed: 0.007 s
% 0.22/0.49  % (20451)------------------------------
% 0.22/0.49  % (20451)------------------------------
% 0.22/0.51  % (20438)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (20466)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (20458)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (20440)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (20436)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (20441)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (20443)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (20457)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (20444)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (20454)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (20450)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (20437)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (20464)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (20465)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (20464)Refutation not found, incomplete strategy% (20464)------------------------------
% 0.22/0.54  % (20464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20464)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20464)Memory used [KB]: 6140
% 0.22/0.54  % (20464)Time elapsed: 0.128 s
% 0.22/0.54  % (20464)------------------------------
% 0.22/0.54  % (20464)------------------------------
% 0.22/0.54  % (20445)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (20439)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (20442)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f2184,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f137,f1672,f1993,f2183])).
% 0.22/0.54  % (20465)Refutation not found, incomplete strategy% (20465)------------------------------
% 0.22/0.54  % (20465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20465)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20465)Memory used [KB]: 10746
% 0.22/0.54  % (20465)Time elapsed: 0.128 s
% 0.22/0.54  % (20465)------------------------------
% 0.22/0.54  % (20465)------------------------------
% 0.22/0.54  fof(f2183,plain,(
% 0.22/0.54    spl5_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f2182])).
% 0.22/0.54  fof(f2182,plain,(
% 0.22/0.54    $false | spl5_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f1748,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    k1_xboole_0 != k4_xboole_0(sK2,sK0) | spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    spl5_1 <=> k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  % (20460)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  fof(f1748,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 0.22/0.54    inference(global_subsumption,[],[f1746])).
% 0.22/0.54  fof(f1746,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 0.22/0.54    inference(global_subsumption,[],[f1656])).
% 0.22/0.54  fof(f1656,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 0.22/0.54    inference(resolution,[],[f1643,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.22/0.54  fof(f1643,plain,(
% 0.22/0.54    ( ! [X4] : (r1_xboole_0(k4_xboole_0(sK2,sK0),X4)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f1625,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    r1_xboole_0(sK1,sK2)),
% 0.22/0.54    inference(resolution,[],[f50,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    r1_xboole_0(sK2,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  % (20461)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.22/0.54    inference(negated_conjecture,[],[f13])).
% 0.22/0.54  fof(f13,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.54  fof(f1625,plain,(
% 0.22/0.54    ( ! [X4] : (r1_xboole_0(k4_xboole_0(sK2,sK0),X4) | ~r1_xboole_0(sK1,sK2)) )),
% 0.22/0.54    inference(resolution,[],[f192,f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(sK2,sK0)) | ~r1_xboole_0(sK1,X0)) )),
% 0.22/0.54    inference(resolution,[],[f76,f50])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK2,sK0),X0) | ~r1_xboole_0(sK1,X0)) )),
% 0.22/0.54    inference(resolution,[],[f74,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    r1_tarski(k4_xboole_0(sK2,sK0),sK1)),
% 0.22/0.54    inference(resolution,[],[f52,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 0.22/0.54    inference(superposition,[],[f41,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    ( ! [X6,X8,X7] : (~r1_xboole_0(X6,k4_xboole_0(X6,X7)) | r1_xboole_0(k4_xboole_0(X6,X7),X8)) )),
% 0.22/0.54    inference(superposition,[],[f79,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f44,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f57,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f46,f43])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.54  fof(f1993,plain,(
% 0.22/0.54    ~spl5_1 | ~spl5_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1992])).
% 0.22/0.54  fof(f1992,plain,(
% 0.22/0.54    $false | (~spl5_1 | ~spl5_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1991,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    sK0 != sK2),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f1991,plain,(
% 0.22/0.54    sK0 = sK2 | (~spl5_1 | ~spl5_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1972,f132])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl5_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f130])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    spl5_5 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.54  fof(f1972,plain,(
% 0.22/0.54    k1_xboole_0 != k4_xboole_0(sK0,sK2) | sK0 = sK2 | ~spl5_1),
% 0.22/0.54    inference(superposition,[],[f51,f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK2,sK0) | ~spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f84])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 0.22/0.54  fof(f1672,plain,(
% 0.22/0.54    spl5_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1671])).
% 0.22/0.54  fof(f1671,plain,(
% 0.22/0.54    $false | spl5_6),
% 0.22/0.54    inference(resolution,[],[f1645,f136])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl5_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f134])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl5_6 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.54  fof(f1645,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(sK0,sK2))) )),
% 0.22/0.54    inference(resolution,[],[f1642,f324])).
% 0.22/0.54  fof(f324,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f323])).
% 0.22/0.54  fof(f323,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.22/0.54    inference(resolution,[],[f68,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (~r2_hidden(sK4(X5,X4),X3) | ~r1_xboole_0(X3,X4) | r1_xboole_0(X5,X4)) )),
% 0.22/0.54    inference(resolution,[],[f49,f48])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f1642,plain,(
% 0.22/0.54    ( ! [X3] : (r1_xboole_0(k4_xboole_0(sK0,sK2),X3)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f1624,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    r1_xboole_0(sK1,sK0)),
% 0.22/0.54    inference(resolution,[],[f50,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    r1_xboole_0(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f1624,plain,(
% 0.22/0.54    ( ! [X3] : (r1_xboole_0(k4_xboole_0(sK0,sK2),X3) | ~r1_xboole_0(sK1,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f192,f128])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(sK0,sK2)) | ~r1_xboole_0(sK1,X0)) )),
% 0.22/0.54    inference(resolution,[],[f126,f50])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,sK2),X0) | ~r1_xboole_0(sK1,X0)) )),
% 0.22/0.54    inference(resolution,[],[f122,f53])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.22/0.54    inference(resolution,[],[f75,f41])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK0,sK1)) | r1_tarski(k4_xboole_0(X0,sK2),sK1)) )),
% 0.22/0.54    inference(superposition,[],[f52,f35])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    spl5_5 | ~spl5_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f127,f134,f130])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.22/0.54    inference(resolution,[],[f126,f40])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (20442)------------------------------
% 0.22/0.54  % (20442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20442)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (20442)Memory used [KB]: 11641
% 0.22/0.54  % (20442)Time elapsed: 0.077 s
% 0.22/0.54  % (20442)------------------------------
% 0.22/0.54  % (20442)------------------------------
% 0.22/0.54  % (20462)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (20446)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (20452)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (20432)Success in time 0.183 s
%------------------------------------------------------------------------------
