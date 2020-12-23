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
% DateTime   : Thu Dec  3 12:53:26 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 215 expanded)
%              Number of leaves         :   17 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  277 ( 769 expanded)
%              Number of equality atoms :   69 ( 208 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f109,f174,f252])).

fof(f252,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f237,f38])).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f237,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f188,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f188,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f113,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_1
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f113,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k3_xboole_0(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f76,f76,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

% (30053)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f76,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f66,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f66,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f36,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f174,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f171,f165])).

fof(f165,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0))),sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f102,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f102,plain,
    ( r2_hidden(sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_2
  <=> r2_hidden(sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f171,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0))),sK1)
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f34,f35,f108,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f108,plain,
    ( k1_funct_1(sK1,sK0) != sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_3
  <=> k1_funct_1(sK1,sK0) = sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f109,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f104,f106,f96])).

fof(f104,plain,
    ( k1_funct_1(sK1,sK0) != sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X1] :
      ( k11_relat_1(sK1,sK0) != X1
      | k1_funct_1(sK1,sK0) != sK3(X1,k1_funct_1(sK1,sK0))
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f59,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f59,plain,(
    k11_relat_1(sK1,sK0) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f37,plain,(
    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f94,f100,f96])).

fof(f94,plain,
    ( r2_hidden(sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( k11_relat_1(sK1,sK0) != X0
      | r2_hidden(sK3(X0,k1_funct_1(sK1,sK0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f59,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:22:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (30060)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.50  % (30052)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (30042)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (30043)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (30039)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (30041)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.52  % (30044)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.52  % (30039)Refutation not found, incomplete strategy% (30039)------------------------------
% 1.28/0.52  % (30039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (30039)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (30039)Memory used [KB]: 10618
% 1.28/0.52  % (30039)Time elapsed: 0.105 s
% 1.28/0.52  % (30039)------------------------------
% 1.28/0.52  % (30039)------------------------------
% 1.28/0.52  % (30040)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.53  % (30059)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.53  % (30050)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.53  % (30063)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.53  % (30054)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.53  % (30047)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.54  % (30045)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.54  % (30045)Refutation not found, incomplete strategy% (30045)------------------------------
% 1.38/0.54  % (30045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (30045)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (30045)Memory used [KB]: 10618
% 1.38/0.54  % (30045)Time elapsed: 0.125 s
% 1.38/0.54  % (30045)------------------------------
% 1.38/0.54  % (30045)------------------------------
% 1.38/0.54  % (30056)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.54  % (30055)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.54  % (30062)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.54  % (30037)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.54  % (30058)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.54  % (30065)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (30038)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.54  % (30064)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.54  % (30048)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.55  % (30048)Refutation not found, incomplete strategy% (30048)------------------------------
% 1.38/0.55  % (30048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (30048)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (30048)Memory used [KB]: 10618
% 1.38/0.55  % (30048)Time elapsed: 0.139 s
% 1.38/0.55  % (30048)------------------------------
% 1.38/0.55  % (30048)------------------------------
% 1.38/0.55  % (30057)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  % (30049)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.55  % (30054)Refutation not found, incomplete strategy% (30054)------------------------------
% 1.38/0.55  % (30054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (30054)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (30054)Memory used [KB]: 10618
% 1.38/0.55  % (30054)Time elapsed: 0.138 s
% 1.38/0.55  % (30054)------------------------------
% 1.38/0.55  % (30054)------------------------------
% 1.38/0.55  % (30061)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.56  % (30051)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.56  % (30047)Refutation not found, incomplete strategy% (30047)------------------------------
% 1.38/0.56  % (30047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (30047)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (30047)Memory used [KB]: 10618
% 1.38/0.56  % (30047)Time elapsed: 0.119 s
% 1.38/0.56  % (30047)------------------------------
% 1.38/0.56  % (30047)------------------------------
% 1.38/0.56  % (30066)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.56  % (30063)Refutation found. Thanks to Tanya!
% 1.38/0.56  % SZS status Theorem for theBenchmark
% 1.38/0.56  % SZS output start Proof for theBenchmark
% 1.38/0.56  fof(f255,plain,(
% 1.38/0.56    $false),
% 1.38/0.56    inference(avatar_sat_refutation,[],[f103,f109,f174,f252])).
% 1.38/0.56  fof(f252,plain,(
% 1.38/0.56    ~spl5_1),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f251])).
% 1.38/0.56  fof(f251,plain,(
% 1.38/0.56    $false | ~spl5_1),
% 1.38/0.56    inference(subsumption_resolution,[],[f237,f38])).
% 1.38/0.56  fof(f38,plain,(
% 1.38/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f3])).
% 1.38/0.56  fof(f3,axiom,(
% 1.38/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.38/0.56  fof(f237,plain,(
% 1.38/0.56    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_1),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f188,f42])).
% 1.38/0.56  fof(f42,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f23])).
% 1.38/0.56  fof(f23,plain,(
% 1.38/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.38/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).
% 1.38/0.56  fof(f22,plain,(
% 1.38/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f15,plain,(
% 1.38/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.38/0.56    inference(ennf_transformation,[],[f12])).
% 1.38/0.56  fof(f12,plain,(
% 1.38/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.56    inference(rectify,[],[f2])).
% 1.38/0.56  fof(f2,axiom,(
% 1.38/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.38/0.56  fof(f188,plain,(
% 1.38/0.56    r2_hidden(k1_funct_1(sK1,sK0),k3_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl5_1),
% 1.38/0.56    inference(backward_demodulation,[],[f113,f98])).
% 1.38/0.56  fof(f98,plain,(
% 1.38/0.56    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl5_1),
% 1.38/0.56    inference(avatar_component_clause,[],[f96])).
% 1.38/0.56  fof(f96,plain,(
% 1.38/0.56    spl5_1 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.38/0.56  fof(f113,plain,(
% 1.38/0.56    r2_hidden(k1_funct_1(sK1,sK0),k3_xboole_0(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0)))),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f76,f76,f63])).
% 1.38/0.56  fof(f63,plain,(
% 1.38/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.38/0.56    inference(equality_resolution,[],[f53])).
% 1.38/0.56  fof(f53,plain,(
% 1.38/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.38/0.56    inference(cnf_transformation,[],[f33])).
% 1.38/0.56  % (30053)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.56  fof(f33,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.38/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 1.38/0.56  fof(f32,plain,(
% 1.38/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f31,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.38/0.56    inference(rectify,[],[f30])).
% 1.38/0.56  fof(f30,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.38/0.56    inference(flattening,[],[f29])).
% 1.38/0.56  fof(f29,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.38/0.56    inference(nnf_transformation,[],[f1])).
% 1.38/0.56  fof(f1,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.38/0.56  fof(f76,plain,(
% 1.38/0.56    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f34,f66,f46])).
% 1.38/0.56  fof(f46,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f26])).
% 1.38/0.56  fof(f26,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 1.38/0.56    inference(nnf_transformation,[],[f17])).
% 1.38/0.56  fof(f17,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.38/0.56    inference(ennf_transformation,[],[f8])).
% 1.38/0.56  fof(f8,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 1.38/0.56  fof(f66,plain,(
% 1.38/0.56    r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1)),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f34,f35,f36,f62])).
% 1.38/0.56  fof(f62,plain,(
% 1.38/0.56    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.38/0.56    inference(equality_resolution,[],[f50])).
% 1.38/0.56  fof(f50,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f28])).
% 1.38/0.56  fof(f28,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.56    inference(flattening,[],[f27])).
% 1.38/0.56  fof(f27,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.56    inference(nnf_transformation,[],[f19])).
% 1.38/0.56  fof(f19,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.56    inference(flattening,[],[f18])).
% 1.38/0.56  fof(f18,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.38/0.56    inference(ennf_transformation,[],[f9])).
% 1.38/0.56  fof(f9,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.38/0.56  fof(f36,plain,(
% 1.38/0.56    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.38/0.56    inference(cnf_transformation,[],[f21])).
% 1.38/0.56  fof(f21,plain,(
% 1.38/0.56    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.38/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).
% 1.38/0.56  fof(f20,plain,(
% 1.38/0.56    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f14,plain,(
% 1.38/0.56    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.38/0.56    inference(flattening,[],[f13])).
% 1.38/0.56  fof(f13,plain,(
% 1.38/0.56    ? [X0,X1] : ((k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.38/0.56    inference(ennf_transformation,[],[f11])).
% 1.38/0.56  fof(f11,negated_conjecture,(
% 1.38/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.38/0.56    inference(negated_conjecture,[],[f10])).
% 1.38/0.56  fof(f10,conjecture,(
% 1.38/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 1.38/0.56  fof(f35,plain,(
% 1.38/0.56    v1_funct_1(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f21])).
% 1.38/0.56  fof(f34,plain,(
% 1.38/0.56    v1_relat_1(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f21])).
% 1.38/0.56  fof(f174,plain,(
% 1.38/0.56    ~spl5_2 | spl5_3),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f173])).
% 1.38/0.56  fof(f173,plain,(
% 1.38/0.56    $false | (~spl5_2 | spl5_3)),
% 1.38/0.56    inference(subsumption_resolution,[],[f171,f165])).
% 1.38/0.56  fof(f165,plain,(
% 1.38/0.56    r2_hidden(k4_tarski(sK0,sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0))),sK1) | ~spl5_2),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f34,f102,f47])).
% 1.38/0.56  fof(f47,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f26])).
% 1.38/0.56  fof(f102,plain,(
% 1.38/0.56    r2_hidden(sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0)) | ~spl5_2),
% 1.38/0.56    inference(avatar_component_clause,[],[f100])).
% 1.38/0.56  fof(f100,plain,(
% 1.38/0.56    spl5_2 <=> r2_hidden(sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.38/0.56  fof(f171,plain,(
% 1.38/0.56    ~r2_hidden(k4_tarski(sK0,sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0))),sK1) | spl5_3),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f34,f35,f108,f49])).
% 1.38/0.56  fof(f49,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f28])).
% 1.38/0.56  fof(f108,plain,(
% 1.38/0.56    k1_funct_1(sK1,sK0) != sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)) | spl5_3),
% 1.38/0.56    inference(avatar_component_clause,[],[f106])).
% 1.38/0.56  fof(f106,plain,(
% 1.38/0.56    spl5_3 <=> k1_funct_1(sK1,sK0) = sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.38/0.56  fof(f109,plain,(
% 1.38/0.56    spl5_1 | ~spl5_3),
% 1.38/0.56    inference(avatar_split_clause,[],[f104,f106,f96])).
% 1.38/0.56  fof(f104,plain,(
% 1.38/0.56    k1_funct_1(sK1,sK0) != sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.38/0.56    inference(equality_resolution,[],[f71])).
% 1.38/0.56  fof(f71,plain,(
% 1.38/0.56    ( ! [X1] : (k11_relat_1(sK1,sK0) != X1 | k1_funct_1(sK1,sK0) != sK3(X1,k1_funct_1(sK1,sK0)) | k1_xboole_0 = X1) )),
% 1.38/0.56    inference(superposition,[],[f59,f60])).
% 1.38/0.56  fof(f60,plain,(
% 1.38/0.56    ( ! [X0,X1] : (sK3(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.38/0.56    inference(definition_unfolding,[],[f44,f58])).
% 1.38/0.56  fof(f58,plain,(
% 1.38/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.38/0.56    inference(definition_unfolding,[],[f39,f57])).
% 1.38/0.56  fof(f57,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.38/0.56    inference(definition_unfolding,[],[f40,f45])).
% 1.38/0.56  fof(f45,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f6])).
% 1.38/0.56  fof(f6,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.38/0.56  fof(f40,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f5])).
% 1.38/0.56  fof(f5,axiom,(
% 1.38/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.38/0.56  fof(f39,plain,(
% 1.38/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f4])).
% 1.38/0.56  fof(f4,axiom,(
% 1.38/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.38/0.56  fof(f44,plain,(
% 1.38/0.56    ( ! [X0,X1] : (sK3(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.38/0.56    inference(cnf_transformation,[],[f25])).
% 1.38/0.56  fof(f25,plain,(
% 1.38/0.56    ! [X0,X1] : ((sK3(X0,X1) != X1 & r2_hidden(sK3(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.38/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f24])).
% 1.38/0.56  fof(f24,plain,(
% 1.38/0.56    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK3(X0,X1) != X1 & r2_hidden(sK3(X0,X1),X0)))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f16,plain,(
% 1.38/0.56    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.38/0.56    inference(ennf_transformation,[],[f7])).
% 1.38/0.56  fof(f7,axiom,(
% 1.38/0.56    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 1.38/0.56  fof(f59,plain,(
% 1.38/0.56    k11_relat_1(sK1,sK0) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.38/0.56    inference(definition_unfolding,[],[f37,f58])).
% 1.38/0.56  fof(f37,plain,(
% 1.38/0.56    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.38/0.56    inference(cnf_transformation,[],[f21])).
% 1.38/0.56  fof(f103,plain,(
% 1.38/0.56    spl5_1 | spl5_2),
% 1.38/0.56    inference(avatar_split_clause,[],[f94,f100,f96])).
% 1.38/0.56  fof(f94,plain,(
% 1.38/0.56    r2_hidden(sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.38/0.56    inference(equality_resolution,[],[f70])).
% 1.38/0.56  fof(f70,plain,(
% 1.38/0.56    ( ! [X0] : (k11_relat_1(sK1,sK0) != X0 | r2_hidden(sK3(X0,k1_funct_1(sK1,sK0)),X0) | k1_xboole_0 = X0) )),
% 1.38/0.56    inference(superposition,[],[f59,f61])).
% 1.38/0.56  fof(f61,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.38/0.56    inference(definition_unfolding,[],[f43,f58])).
% 1.38/0.56  fof(f43,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.38/0.56    inference(cnf_transformation,[],[f25])).
% 1.38/0.56  % SZS output end Proof for theBenchmark
% 1.38/0.56  % (30063)------------------------------
% 1.38/0.56  % (30063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (30063)Termination reason: Refutation
% 1.38/0.56  
% 1.38/0.56  % (30063)Memory used [KB]: 10874
% 1.38/0.56  % (30063)Time elapsed: 0.152 s
% 1.38/0.56  % (30063)------------------------------
% 1.38/0.56  % (30063)------------------------------
% 1.38/0.56  % (30036)Success in time 0.195 s
%------------------------------------------------------------------------------
