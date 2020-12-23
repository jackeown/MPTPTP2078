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
% DateTime   : Thu Dec  3 12:53:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 195 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  287 ( 648 expanded)
%              Number of equality atoms :   54 ( 140 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f421,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f76,f334,f345,f354,f420])).

fof(f420,plain,
    ( ~ spl5_1
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(resolution,[],[f385,f69])).

fof(f69,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_1
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f385,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl5_7 ),
    inference(superposition,[],[f101,f357])).

fof(f357,plain,
    ( k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_7 ),
    inference(resolution,[],[f353,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f353,plain,
    ( r1_xboole_0(k2_relat_1(sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f351])).

% (18405)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f351,plain,
    ( spl5_7
  <=> r1_xboole_0(k2_relat_1(sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f101,plain,(
    ! [X8,X7,X9] : ~ r2_hidden(X7,k4_xboole_0(X8,k3_enumset1(X7,X7,X7,X7,X9))) ),
    inference(resolution,[],[f96,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f57,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

% (18408)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f96,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X0))
      | r1_xboole_0(X0,k4_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f86,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f86,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK3(X3,k4_xboole_0(X4,X5)),X5)
      | r1_xboole_0(X3,k4_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f84,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f50,f66])).

fof(f66,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f354,plain,
    ( ~ spl5_5
    | spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f349,f72,f351,f324])).

fof(f324,plain,
    ( spl5_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f72,plain,
    ( spl5_2
  <=> k1_xboole_0 = k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f349,plain,
    ( r1_xboole_0(k2_relat_1(sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f348])).

fof(f348,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(superposition,[],[f43,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k10_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k10_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f345,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl5_1
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f341])).

fof(f341,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl5_1
    | spl5_2 ),
    inference(superposition,[],[f73,f287])).

fof(f287,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl5_1 ),
    inference(superposition,[],[f134,f269])).

fof(f269,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2))
    | spl5_1 ),
    inference(resolution,[],[f89,f70])).

fof(f70,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f89,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,X4)
      | k3_enumset1(X3,X3,X3,X3,X3) = k4_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),X4) ) ),
    inference(resolution,[],[f64,f46])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f134,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(X0,k2_relat_1(sK2))) ),
    inference(resolution,[],[f100,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
      | ~ r2_hidden(sK1,k2_relat_1(sK2)) )
    & ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1))
      | r2_hidden(sK1,k2_relat_1(sK2)) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
        | ~ r2_hidden(sK1,k2_relat_1(sK2)) )
      & ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1))
        | r2_hidden(sK1,k2_relat_1(sK2)) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f100,plain,(
    ! [X6,X5] :
      ( ~ v1_relat_1(X5)
      | k1_xboole_0 = k10_relat_1(X5,k4_xboole_0(X6,k2_relat_1(X5))) ) ),
    inference(resolution,[],[f96,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f334,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f326,f35])).

fof(f326,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f324])).

fof(f76,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f63,f72,f68])).

fof(f63,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(definition_unfolding,[],[f36,f61])).

fof(f36,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1))
    | r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f62,f72,f68])).

fof(f62,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(definition_unfolding,[],[f37,f61])).

fof(f37,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (18401)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (18417)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (18409)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (18404)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (18417)Refutation not found, incomplete strategy% (18417)------------------------------
% 0.20/0.52  % (18417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18417)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18417)Memory used [KB]: 10618
% 0.20/0.52  % (18417)Time elapsed: 0.059 s
% 0.20/0.52  % (18417)------------------------------
% 0.20/0.52  % (18417)------------------------------
% 0.20/0.52  % (18398)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (18407)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (18400)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (18407)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (18413)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (18397)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (18397)Refutation not found, incomplete strategy% (18397)------------------------------
% 0.20/0.54  % (18397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18397)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18397)Memory used [KB]: 10618
% 0.20/0.54  % (18397)Time elapsed: 0.128 s
% 0.20/0.54  % (18397)------------------------------
% 0.20/0.54  % (18397)------------------------------
% 0.20/0.54  % (18421)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (18420)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (18395)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (18396)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (18402)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (18403)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (18403)Refutation not found, incomplete strategy% (18403)------------------------------
% 0.20/0.54  % (18403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18403)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18403)Memory used [KB]: 10618
% 0.20/0.54  % (18403)Time elapsed: 0.134 s
% 0.20/0.54  % (18403)------------------------------
% 0.20/0.54  % (18403)------------------------------
% 0.20/0.55  % (18419)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (18414)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (18418)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (18412)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f421,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f75,f76,f334,f345,f354,f420])).
% 0.20/0.56  fof(f420,plain,(
% 0.20/0.56    ~spl5_1 | ~spl5_7),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f417])).
% 0.20/0.56  fof(f417,plain,(
% 0.20/0.56    $false | (~spl5_1 | ~spl5_7)),
% 0.20/0.56    inference(resolution,[],[f385,f69])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl5_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f68])).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    spl5_1 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.56  fof(f385,plain,(
% 0.20/0.56    ~r2_hidden(sK1,k2_relat_1(sK2)) | ~spl5_7),
% 0.20/0.56    inference(superposition,[],[f101,f357])).
% 0.20/0.56  fof(f357,plain,(
% 0.20/0.56    k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl5_7),
% 0.20/0.56    inference(resolution,[],[f353,f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.56  fof(f353,plain,(
% 0.20/0.56    r1_xboole_0(k2_relat_1(sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl5_7),
% 0.20/0.56    inference(avatar_component_clause,[],[f351])).
% 0.20/0.56  % (18405)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  fof(f351,plain,(
% 0.20/0.56    spl5_7 <=> r1_xboole_0(k2_relat_1(sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.56  fof(f101,plain,(
% 0.20/0.56    ( ! [X8,X7,X9] : (~r2_hidden(X7,k4_xboole_0(X8,k3_enumset1(X7,X7,X7,X7,X9)))) )),
% 0.20/0.56    inference(resolution,[],[f96,f65])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f57,f60])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f39,f59])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f48,f58])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.56  % (18408)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f94])).
% 0.20/0.56  fof(f94,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0)) | r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.56    inference(resolution,[],[f86,f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ( ! [X4,X5,X3] : (~r2_hidden(sK3(X3,k4_xboole_0(X4,X5)),X5) | r1_xboole_0(X3,k4_xboole_0(X4,X5))) )),
% 0.20/0.56    inference(resolution,[],[f84,f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 0.20/0.56    inference(resolution,[],[f50,f66])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(equality_resolution,[],[f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.56    inference(nnf_transformation,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.20/0.56    inference(definition_folding,[],[f1,f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.56    inference(rectify,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.56    inference(flattening,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.56    inference(nnf_transformation,[],[f19])).
% 0.20/0.56  fof(f354,plain,(
% 0.20/0.56    ~spl5_5 | spl5_7 | ~spl5_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f349,f72,f351,f324])).
% 0.20/0.56  fof(f324,plain,(
% 0.20/0.56    spl5_5 <=> v1_relat_1(sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    spl5_2 <=> k1_xboole_0 = k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.56  fof(f349,plain,(
% 0.20/0.56    r1_xboole_0(k2_relat_1(sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~v1_relat_1(sK2) | ~spl5_2),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f348])).
% 0.20/0.56  fof(f348,plain,(
% 0.20/0.56    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~v1_relat_1(sK2) | ~spl5_2),
% 0.20/0.56    inference(superposition,[],[f43,f74])).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    k1_xboole_0 = k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl5_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f72])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k10_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0,X1] : (((k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.20/0.56  fof(f345,plain,(
% 0.20/0.56    spl5_1 | spl5_2),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f344])).
% 0.20/0.56  fof(f344,plain,(
% 0.20/0.56    $false | (spl5_1 | spl5_2)),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f341])).
% 0.20/0.56  fof(f341,plain,(
% 0.20/0.56    k1_xboole_0 != k1_xboole_0 | (spl5_1 | spl5_2)),
% 0.20/0.56    inference(superposition,[],[f73,f287])).
% 0.20/0.56  fof(f287,plain,(
% 0.20/0.56    k1_xboole_0 = k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl5_1),
% 0.20/0.56    inference(superposition,[],[f134,f269])).
% 0.20/0.56  fof(f269,plain,(
% 0.20/0.56    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2)) | spl5_1),
% 0.20/0.56    inference(resolution,[],[f89,f70])).
% 0.20/0.56  fof(f70,plain,(
% 0.20/0.56    ~r2_hidden(sK1,k2_relat_1(sK2)) | spl5_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f68])).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    ( ! [X4,X3] : (r2_hidden(X3,X4) | k3_enumset1(X3,X3,X3,X3,X3) = k4_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),X4)) )),
% 0.20/0.56    inference(resolution,[],[f64,f46])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f45,f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f38,f60])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.56  fof(f134,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(X0,k2_relat_1(sK2)))) )),
% 0.20/0.56    inference(resolution,[],[f100,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    v1_relat_1(sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    (k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) | ~r2_hidden(sK1,k2_relat_1(sK2))) & (k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1)) | r2_hidden(sK1,k2_relat_1(sK2))) & v1_relat_1(sK2)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) | ~r2_hidden(sK1,k2_relat_1(sK2))) & (k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1)) | r2_hidden(sK1,k2_relat_1(sK2))) & v1_relat_1(sK2))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.56    inference(flattening,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.20/0.56    inference(negated_conjecture,[],[f11])).
% 0.20/0.56  fof(f11,conjecture,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.20/0.56  fof(f100,plain,(
% 0.20/0.56    ( ! [X6,X5] : (~v1_relat_1(X5) | k1_xboole_0 = k10_relat_1(X5,k4_xboole_0(X6,k2_relat_1(X5)))) )),
% 0.20/0.56    inference(resolution,[],[f96,f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) = k1_xboole_0 | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    k1_xboole_0 != k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl5_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f72])).
% 0.20/0.56  fof(f334,plain,(
% 0.20/0.56    spl5_5),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f333])).
% 0.20/0.56  fof(f333,plain,(
% 0.20/0.56    $false | spl5_5),
% 0.20/0.56    inference(resolution,[],[f326,f35])).
% 0.20/0.56  fof(f326,plain,(
% 0.20/0.56    ~v1_relat_1(sK2) | spl5_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f324])).
% 0.20/0.56  fof(f76,plain,(
% 0.20/0.56    spl5_1 | ~spl5_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f63,f72,f68])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    k1_xboole_0 != k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | r2_hidden(sK1,k2_relat_1(sK2))),
% 0.20/0.56    inference(definition_unfolding,[],[f36,f61])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1)) | r2_hidden(sK1,k2_relat_1(sK2))),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f75,plain,(
% 0.20/0.56    ~spl5_1 | spl5_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f62,f72,f68])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    k1_xboole_0 = k10_relat_1(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,k2_relat_1(sK2))),
% 0.20/0.56    inference(definition_unfolding,[],[f37,f61])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) | ~r2_hidden(sK1,k2_relat_1(sK2))),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (18407)------------------------------
% 0.20/0.56  % (18407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18407)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (18407)Memory used [KB]: 6524
% 0.20/0.56  % (18407)Time elapsed: 0.106 s
% 0.20/0.56  % (18407)------------------------------
% 0.20/0.56  % (18407)------------------------------
% 0.20/0.56  % (18405)Refutation not found, incomplete strategy% (18405)------------------------------
% 0.20/0.56  % (18405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18405)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18405)Memory used [KB]: 10618
% 0.20/0.56  % (18405)Time elapsed: 0.151 s
% 0.20/0.56  % (18405)------------------------------
% 0.20/0.56  % (18405)------------------------------
% 0.20/0.56  % (18394)Success in time 0.198 s
%------------------------------------------------------------------------------
