%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t71_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:31 EDT 2019

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 250 expanded)
%              Number of leaves         :   17 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  368 (1251 expanded)
%              Number of equality atoms :   54 ( 219 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4630,f4639,f4691,f4853,f4861,f5000,f5175])).

fof(f5175,plain,
    ( ~ spl6_161
    | spl6_66
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f5174,f4625,f693,f4851])).

fof(f4851,plain,
    ( spl6_161
  <=> ~ r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_161])])).

fof(f693,plain,
    ( spl6_66
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f4625,plain,
    ( spl6_64
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f5174,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2)
    | ~ spl6_64 ),
    inference(resolution,[],[f4626,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t71_xboole_1.p',d10_xboole_0)).

fof(f4626,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f4625])).

fof(f5000,plain,(
    ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f4863])).

fof(f4863,plain,
    ( $false
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f56,f694])).

fof(f694,plain,
    ( sK0 = sK2
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f693])).

fof(f56,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f34])).

fof(f34,plain,
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

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t71_xboole_1.p',t71_xboole_1)).

fof(f4861,plain,(
    spl6_161 ),
    inference(avatar_contradiction_clause,[],[f4858])).

fof(f4858,plain,
    ( $false
    | ~ spl6_161 ),
    inference(subsumption_resolution,[],[f4852,f4855])).

fof(f4855,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl6_161 ),
    inference(resolution,[],[f4854,f894])).

fof(f894,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3(X2,sK2),sK0)
      | r1_tarski(X2,sK2) ) ),
    inference(global_subsumption,[],[f589,f279])).

fof(f279,plain,(
    ! [X2] :
      ( r2_hidden(sK3(X2,sK2),sK1)
      | ~ r2_hidden(sK3(X2,sK2),sK0)
      | r1_tarski(X2,sK2) ) ),
    inference(resolution,[],[f160,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t71_xboole_1.p',d3_tarski)).

fof(f160,plain,(
    ! [X9] :
      ( r2_hidden(X9,sK2)
      | r2_hidden(X9,sK1)
      | ~ r2_hidden(X9,sK0) ) ),
    inference(resolution,[],[f102,f96])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t71_xboole_1.p',d3_xboole_0)).

fof(f102,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK0,sK1))
      | r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f97,f53])).

fof(f53,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f589,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK2)
      | ~ r2_hidden(sK3(X1,sK2),sK1)
      | ~ r2_hidden(sK3(X1,sK2),sK0) ) ),
    inference(resolution,[],[f200,f110])).

fof(f110,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f92,f98])).

fof(f98,plain,(
    k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(resolution,[],[f54,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t71_xboole_1.p',d7_xboole_0)).

fof(f54,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f46,plain,(
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

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t71_xboole_1.p',d4_xboole_0)).

fof(f200,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3(X2,sK2),k1_xboole_0)
      | r1_tarski(X2,sK2) ) ),
    inference(resolution,[],[f115,f73])).

fof(f115,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f94,f99])).

fof(f99,plain,(
    k3_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(resolution,[],[f55,f74])).

fof(f55,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4854,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | ~ spl6_161 ),
    inference(resolution,[],[f4852,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4852,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl6_161 ),
    inference(avatar_component_clause,[],[f4851])).

fof(f4853,plain,
    ( ~ spl6_161
    | spl6_66
    | ~ spl6_158 ),
    inference(avatar_split_clause,[],[f4848,f4637,f693,f4851])).

fof(f4637,plain,
    ( spl6_158
  <=> r2_hidden(sK3(sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_158])])).

fof(f4848,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2)
    | ~ spl6_158 ),
    inference(resolution,[],[f4843,f70])).

fof(f4843,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl6_158 ),
    inference(resolution,[],[f4638,f73])).

fof(f4638,plain,
    ( r2_hidden(sK3(sK2,sK0),sK0)
    | ~ spl6_158 ),
    inference(avatar_component_clause,[],[f4637])).

fof(f4691,plain,
    ( spl6_65
    | spl6_157 ),
    inference(avatar_contradiction_clause,[],[f4688])).

fof(f4688,plain,
    ( $false
    | ~ spl6_65
    | ~ spl6_157 ),
    inference(subsumption_resolution,[],[f779,f4635])).

fof(f4635,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),sK2)
    | ~ spl6_157 ),
    inference(avatar_component_clause,[],[f4634])).

fof(f4634,plain,
    ( spl6_157
  <=> ~ r2_hidden(sK3(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_157])])).

fof(f779,plain,
    ( r2_hidden(sK3(sK2,sK0),sK2)
    | ~ spl6_65 ),
    inference(resolution,[],[f691,f72])).

fof(f691,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f690])).

fof(f690,plain,
    ( spl6_65
  <=> ~ r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f4639,plain,
    ( ~ spl6_157
    | spl6_158
    | spl6_155 ),
    inference(avatar_split_clause,[],[f4631,f4628,f4637,f4634])).

fof(f4628,plain,
    ( spl6_155
  <=> ~ r2_hidden(sK3(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_155])])).

fof(f4631,plain,
    ( r2_hidden(sK3(sK2,sK0),sK0)
    | ~ r2_hidden(sK3(sK2,sK0),sK2)
    | ~ spl6_155 ),
    inference(resolution,[],[f4629,f141])).

fof(f141,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f103,f97])).

fof(f103,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(superposition,[],[f96,f53])).

fof(f4629,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),sK1)
    | ~ spl6_155 ),
    inference(avatar_component_clause,[],[f4628])).

fof(f4630,plain,
    ( spl6_64
    | ~ spl6_155
    | spl6_65 ),
    inference(avatar_split_clause,[],[f4621,f690,f4628,f4625])).

fof(f4621,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),sK1)
    | r1_tarski(sK2,sK0)
    | ~ spl6_65 ),
    inference(resolution,[],[f584,f779])).

fof(f584,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,sK0),sK2)
      | ~ r2_hidden(sK3(X0,sK0),sK1)
      | r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f177,f117])).

fof(f117,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,sK2) ) ),
    inference(superposition,[],[f92,f99])).

fof(f177,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3(X2,sK0),k1_xboole_0)
      | r1_tarski(X2,sK0) ) ),
    inference(resolution,[],[f108,f73])).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f94,f98])).
%------------------------------------------------------------------------------
