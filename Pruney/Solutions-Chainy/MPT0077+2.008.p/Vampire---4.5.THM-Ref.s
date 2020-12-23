%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:44 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 282 expanded)
%              Number of leaves         :   11 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  281 (1405 expanded)
%              Number of equality atoms :   14 (  86 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1600,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f66,f333,f743,f1598])).

fof(f1598,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f1597])).

fof(f1597,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f1596,f803])).

fof(f803,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f754,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f754,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f58,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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

fof(f58,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1596,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f1574,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1574,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK0,sK1),sK2))
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f792,f864,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f864,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f753,f791,f49])).

fof(f791,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f339,f753,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f339,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f64,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f64,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f753,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f58,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f792,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f749,f753,f36])).

fof(f749,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f55,f37])).

fof(f55,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f743,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f742])).

fof(f742,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f740,f727])).

fof(f727,plain,
    ( ! [X6,X7] : ~ r2_hidden(sK3(sK2,sK0),k4_xboole_0(X6,k2_xboole_0(X7,sK2)))
    | spl5_1 ),
    inference(superposition,[],[f394,f40])).

fof(f394,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK2,sK0),k4_xboole_0(X0,sK2))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f342,f50])).

fof(f342,plain,
    ( r2_hidden(sK3(sK2,sK0),sK2)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f335,f34])).

fof(f335,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f54,f37])).

fof(f54,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f740,plain,
    ( r2_hidden(sK3(sK2,sK0),k4_xboole_0(sK2,k2_xboole_0(sK1,sK2)))
    | spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f342,f402,f49])).

fof(f402,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),k2_xboole_0(sK1,sK2))
    | spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f76,f343,f36])).

fof(f343,plain,
    ( r2_hidden(sK3(sK2,sK0),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f335,f35])).

fof(f76,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f59,f37])).

fof(f59,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f333,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f328,f317])).

fof(f317,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK3(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(sK1,X1)))
    | spl5_3 ),
    inference(forward_demodulation,[],[f310,f40])).

fof(f310,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK3(sK1,sK0),k4_xboole_0(k4_xboole_0(X0,sK1),X1))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f136,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f136,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK1,sK0),k4_xboole_0(X0,sK1))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f73,f50])).

fof(f73,plain,
    ( r2_hidden(sK3(sK1,sK0),sK1)
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f68,f34])).

fof(f68,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f63,f37])).

fof(f63,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f328,plain,
    ( r2_hidden(sK3(sK1,sK0),k4_xboole_0(sK1,k2_xboole_0(sK1,sK2)))
    | ~ spl5_2
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f73,f143,f49])).

fof(f143,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),k2_xboole_0(sK1,sK2))
    | ~ spl5_2
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f76,f74,f36])).

fof(f74,plain,
    ( r2_hidden(sK3(sK1,sK0),sK0)
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f68,f35])).

fof(f66,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f25,f53,f62,f57])).

fof(f25,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f65,plain,
    ( spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f29,f57,f62])).

fof(f29,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f30,f57,f53])).

fof(f30,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:57:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (8842)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (8845)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (8853)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (8866)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (8858)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (8841)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (8861)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (8849)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (8840)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (8839)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (8839)Refutation not found, incomplete strategy% (8839)------------------------------
% 0.21/0.53  % (8839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8839)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8839)Memory used [KB]: 1663
% 0.21/0.53  % (8839)Time elapsed: 0.124 s
% 0.21/0.53  % (8839)------------------------------
% 0.21/0.53  % (8839)------------------------------
% 0.21/0.53  % (8850)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (8849)Refutation not found, incomplete strategy% (8849)------------------------------
% 0.21/0.53  % (8849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8843)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (8844)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (8855)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (8848)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (8867)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (8868)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (8857)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (8847)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (8851)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (8860)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (8846)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (8865)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (8863)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (8864)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (8856)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (8859)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (8849)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8849)Memory used [KB]: 10618
% 0.21/0.54  % (8849)Time elapsed: 0.131 s
% 0.21/0.54  % (8849)------------------------------
% 0.21/0.54  % (8849)------------------------------
% 0.21/0.54  % (8856)Refutation not found, incomplete strategy% (8856)------------------------------
% 0.21/0.54  % (8856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8856)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8856)Memory used [KB]: 10618
% 0.21/0.54  % (8856)Time elapsed: 0.148 s
% 0.21/0.54  % (8856)------------------------------
% 0.21/0.54  % (8856)------------------------------
% 0.21/0.54  % (8854)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (8862)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (8852)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (8848)Refutation not found, incomplete strategy% (8848)------------------------------
% 0.21/0.55  % (8848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8848)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (8848)Memory used [KB]: 10618
% 0.21/0.55  % (8848)Time elapsed: 0.148 s
% 0.21/0.55  % (8848)------------------------------
% 0.21/0.55  % (8848)------------------------------
% 2.12/0.65  % (8893)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.12/0.65  % (8893)Refutation not found, incomplete strategy% (8893)------------------------------
% 2.12/0.65  % (8893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.66  % (8893)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.66  
% 2.12/0.66  % (8893)Memory used [KB]: 6140
% 2.12/0.66  % (8893)Time elapsed: 0.096 s
% 2.12/0.66  % (8893)------------------------------
% 2.12/0.66  % (8893)------------------------------
% 2.12/0.67  % (8901)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.12/0.68  % (8900)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.12/0.69  % (8865)Refutation found. Thanks to Tanya!
% 2.12/0.69  % SZS status Theorem for theBenchmark
% 2.12/0.70  % (8908)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.69/0.71  % SZS output start Proof for theBenchmark
% 2.69/0.71  fof(f1600,plain,(
% 2.69/0.71    $false),
% 2.69/0.71    inference(avatar_sat_refutation,[],[f60,f65,f66,f333,f743,f1598])).
% 2.69/0.71  fof(f1598,plain,(
% 2.69/0.71    ~spl5_1 | spl5_2 | ~spl5_3),
% 2.69/0.71    inference(avatar_contradiction_clause,[],[f1597])).
% 2.69/0.71  fof(f1597,plain,(
% 2.69/0.71    $false | (~spl5_1 | spl5_2 | ~spl5_3)),
% 2.69/0.71    inference(subsumption_resolution,[],[f1596,f803])).
% 2.69/0.71  fof(f803,plain,(
% 2.69/0.71    ( ! [X0] : (~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) ) | spl5_2),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f754,f50])).
% 2.69/0.71  fof(f50,plain,(
% 2.69/0.71    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.69/0.71    inference(equality_resolution,[],[f42])).
% 2.69/0.71  fof(f42,plain,(
% 2.69/0.71    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.69/0.71    inference(cnf_transformation,[],[f24])).
% 2.69/0.71  fof(f24,plain,(
% 2.69/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.69/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 2.69/0.71  fof(f23,plain,(
% 2.69/0.71    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.69/0.71    introduced(choice_axiom,[])).
% 2.69/0.71  fof(f22,plain,(
% 2.69/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.69/0.71    inference(rectify,[],[f21])).
% 2.69/0.71  fof(f21,plain,(
% 2.69/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.69/0.71    inference(flattening,[],[f20])).
% 2.69/0.71  fof(f20,plain,(
% 2.69/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.69/0.71    inference(nnf_transformation,[],[f2])).
% 2.69/0.71  fof(f2,axiom,(
% 2.69/0.71    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.69/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.69/0.71  fof(f754,plain,(
% 2.69/0.71    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) | spl5_2),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f58,f35])).
% 2.69/0.71  fof(f35,plain,(
% 2.69/0.71    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.69/0.71    inference(cnf_transformation,[],[f18])).
% 2.69/0.71  fof(f18,plain,(
% 2.69/0.71    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.69/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f17])).
% 2.69/0.71  fof(f17,plain,(
% 2.69/0.71    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.69/0.71    introduced(choice_axiom,[])).
% 2.69/0.71  fof(f13,plain,(
% 2.69/0.71    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.69/0.71    inference(ennf_transformation,[],[f11])).
% 2.69/0.71  fof(f11,plain,(
% 2.69/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.69/0.71    inference(rectify,[],[f5])).
% 2.69/0.71  fof(f5,axiom,(
% 2.69/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.69/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.69/0.71  fof(f58,plain,(
% 2.69/0.71    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl5_2),
% 2.69/0.71    inference(avatar_component_clause,[],[f57])).
% 2.69/0.71  fof(f57,plain,(
% 2.69/0.71    spl5_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.69/0.71  fof(f1596,plain,(
% 2.69/0.71    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | (~spl5_1 | spl5_2 | ~spl5_3)),
% 2.69/0.71    inference(forward_demodulation,[],[f1574,f40])).
% 2.69/0.71  fof(f40,plain,(
% 2.69/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.69/0.71    inference(cnf_transformation,[],[f7])).
% 2.69/0.71  fof(f7,axiom,(
% 2.69/0.71    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.69/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.69/0.71  fof(f1574,plain,(
% 2.69/0.71    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)) | (~spl5_1 | spl5_2 | ~spl5_3)),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f792,f864,f49])).
% 2.69/0.71  fof(f49,plain,(
% 2.69/0.71    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.69/0.71    inference(equality_resolution,[],[f43])).
% 2.69/0.71  fof(f43,plain,(
% 2.69/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.69/0.71    inference(cnf_transformation,[],[f24])).
% 2.69/0.71  fof(f864,plain,(
% 2.69/0.71    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | (spl5_2 | ~spl5_3)),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f753,f791,f49])).
% 2.69/0.71  fof(f791,plain,(
% 2.69/0.71    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | (spl5_2 | ~spl5_3)),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f339,f753,f36])).
% 2.69/0.71  fof(f36,plain,(
% 2.69/0.71    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.69/0.71    inference(cnf_transformation,[],[f18])).
% 2.69/0.71  fof(f339,plain,(
% 2.69/0.71    r1_xboole_0(sK1,sK0) | ~spl5_3),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f64,f37])).
% 2.69/0.71  fof(f37,plain,(
% 2.69/0.71    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.69/0.71    inference(cnf_transformation,[],[f14])).
% 2.69/0.71  fof(f14,plain,(
% 2.69/0.71    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.69/0.71    inference(ennf_transformation,[],[f4])).
% 2.69/0.71  fof(f4,axiom,(
% 2.69/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.69/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.69/0.71  fof(f64,plain,(
% 2.69/0.71    r1_xboole_0(sK0,sK1) | ~spl5_3),
% 2.69/0.71    inference(avatar_component_clause,[],[f62])).
% 2.69/0.71  fof(f62,plain,(
% 2.69/0.71    spl5_3 <=> r1_xboole_0(sK0,sK1)),
% 2.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.69/0.71  fof(f753,plain,(
% 2.69/0.71    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | spl5_2),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f58,f34])).
% 2.69/0.71  fof(f34,plain,(
% 2.69/0.71    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.69/0.71    inference(cnf_transformation,[],[f18])).
% 2.69/0.71  fof(f792,plain,(
% 2.69/0.71    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | (~spl5_1 | spl5_2)),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f749,f753,f36])).
% 2.69/0.71  fof(f749,plain,(
% 2.69/0.71    r1_xboole_0(sK2,sK0) | ~spl5_1),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f55,f37])).
% 2.69/0.71  fof(f55,plain,(
% 2.69/0.71    r1_xboole_0(sK0,sK2) | ~spl5_1),
% 2.69/0.71    inference(avatar_component_clause,[],[f53])).
% 2.69/0.71  fof(f53,plain,(
% 2.69/0.71    spl5_1 <=> r1_xboole_0(sK0,sK2)),
% 2.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.69/0.71  fof(f743,plain,(
% 2.69/0.71    spl5_1 | ~spl5_2),
% 2.69/0.71    inference(avatar_contradiction_clause,[],[f742])).
% 2.69/0.71  fof(f742,plain,(
% 2.69/0.71    $false | (spl5_1 | ~spl5_2)),
% 2.69/0.71    inference(subsumption_resolution,[],[f740,f727])).
% 2.69/0.71  fof(f727,plain,(
% 2.69/0.71    ( ! [X6,X7] : (~r2_hidden(sK3(sK2,sK0),k4_xboole_0(X6,k2_xboole_0(X7,sK2)))) ) | spl5_1),
% 2.69/0.71    inference(superposition,[],[f394,f40])).
% 2.69/0.71  fof(f394,plain,(
% 2.69/0.71    ( ! [X0] : (~r2_hidden(sK3(sK2,sK0),k4_xboole_0(X0,sK2))) ) | spl5_1),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f342,f50])).
% 2.69/0.71  fof(f342,plain,(
% 2.69/0.71    r2_hidden(sK3(sK2,sK0),sK2) | spl5_1),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f335,f34])).
% 2.69/0.71  fof(f335,plain,(
% 2.69/0.71    ~r1_xboole_0(sK2,sK0) | spl5_1),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f54,f37])).
% 2.69/0.71  fof(f54,plain,(
% 2.69/0.71    ~r1_xboole_0(sK0,sK2) | spl5_1),
% 2.69/0.71    inference(avatar_component_clause,[],[f53])).
% 2.69/0.71  fof(f740,plain,(
% 2.69/0.71    r2_hidden(sK3(sK2,sK0),k4_xboole_0(sK2,k2_xboole_0(sK1,sK2))) | (spl5_1 | ~spl5_2)),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f342,f402,f49])).
% 2.69/0.71  fof(f402,plain,(
% 2.69/0.71    ~r2_hidden(sK3(sK2,sK0),k2_xboole_0(sK1,sK2)) | (spl5_1 | ~spl5_2)),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f76,f343,f36])).
% 2.69/0.71  fof(f343,plain,(
% 2.69/0.71    r2_hidden(sK3(sK2,sK0),sK0) | spl5_1),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f335,f35])).
% 2.69/0.71  fof(f76,plain,(
% 2.69/0.71    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl5_2),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f59,f37])).
% 2.69/0.71  fof(f59,plain,(
% 2.69/0.71    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_2),
% 2.69/0.71    inference(avatar_component_clause,[],[f57])).
% 2.69/0.71  fof(f333,plain,(
% 2.69/0.71    ~spl5_2 | spl5_3),
% 2.69/0.71    inference(avatar_contradiction_clause,[],[f332])).
% 2.69/0.71  fof(f332,plain,(
% 2.69/0.71    $false | (~spl5_2 | spl5_3)),
% 2.69/0.71    inference(subsumption_resolution,[],[f328,f317])).
% 2.69/0.71  fof(f317,plain,(
% 2.69/0.71    ( ! [X0,X1] : (~r2_hidden(sK3(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(sK1,X1)))) ) | spl5_3),
% 2.69/0.71    inference(forward_demodulation,[],[f310,f40])).
% 2.69/0.71  fof(f310,plain,(
% 2.69/0.71    ( ! [X0,X1] : (~r2_hidden(sK3(sK1,sK0),k4_xboole_0(k4_xboole_0(X0,sK1),X1))) ) | spl5_3),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f136,f51])).
% 2.69/0.71  fof(f51,plain,(
% 2.69/0.71    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.69/0.71    inference(equality_resolution,[],[f41])).
% 2.69/0.71  fof(f41,plain,(
% 2.69/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.69/0.71    inference(cnf_transformation,[],[f24])).
% 2.69/0.71  fof(f136,plain,(
% 2.69/0.71    ( ! [X0] : (~r2_hidden(sK3(sK1,sK0),k4_xboole_0(X0,sK1))) ) | spl5_3),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f73,f50])).
% 2.69/0.71  fof(f73,plain,(
% 2.69/0.71    r2_hidden(sK3(sK1,sK0),sK1) | spl5_3),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f68,f34])).
% 2.69/0.71  fof(f68,plain,(
% 2.69/0.71    ~r1_xboole_0(sK1,sK0) | spl5_3),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f63,f37])).
% 2.69/0.71  fof(f63,plain,(
% 2.69/0.71    ~r1_xboole_0(sK0,sK1) | spl5_3),
% 2.69/0.71    inference(avatar_component_clause,[],[f62])).
% 2.69/0.71  fof(f328,plain,(
% 2.69/0.71    r2_hidden(sK3(sK1,sK0),k4_xboole_0(sK1,k2_xboole_0(sK1,sK2))) | (~spl5_2 | spl5_3)),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f73,f143,f49])).
% 2.69/0.71  fof(f143,plain,(
% 2.69/0.71    ~r2_hidden(sK3(sK1,sK0),k2_xboole_0(sK1,sK2)) | (~spl5_2 | spl5_3)),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f76,f74,f36])).
% 2.69/0.71  fof(f74,plain,(
% 2.69/0.71    r2_hidden(sK3(sK1,sK0),sK0) | spl5_3),
% 2.69/0.71    inference(unit_resulting_resolution,[],[f68,f35])).
% 2.69/0.71  fof(f66,plain,(
% 2.69/0.71    ~spl5_2 | ~spl5_3 | ~spl5_1),
% 2.69/0.71    inference(avatar_split_clause,[],[f25,f53,f62,f57])).
% 2.69/0.71  fof(f25,plain,(
% 2.69/0.71    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.69/0.71    inference(cnf_transformation,[],[f16])).
% 2.69/0.71  fof(f16,plain,(
% 2.69/0.71    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 2.69/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 2.69/0.71  fof(f15,plain,(
% 2.69/0.71    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 2.69/0.71    introduced(choice_axiom,[])).
% 2.69/0.71  fof(f12,plain,(
% 2.69/0.71    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.69/0.71    inference(ennf_transformation,[],[f10])).
% 2.69/0.71  fof(f10,negated_conjecture,(
% 2.69/0.71    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.69/0.71    inference(negated_conjecture,[],[f9])).
% 2.69/0.71  fof(f9,conjecture,(
% 2.69/0.71    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.69/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.69/0.71  fof(f65,plain,(
% 2.69/0.71    spl5_3 | spl5_2),
% 2.69/0.71    inference(avatar_split_clause,[],[f29,f57,f62])).
% 2.69/0.71  fof(f29,plain,(
% 2.69/0.71    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 2.69/0.71    inference(cnf_transformation,[],[f16])).
% 2.69/0.71  fof(f60,plain,(
% 2.69/0.71    spl5_1 | spl5_2),
% 2.69/0.71    inference(avatar_split_clause,[],[f30,f57,f53])).
% 2.69/0.71  fof(f30,plain,(
% 2.69/0.71    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 2.69/0.71    inference(cnf_transformation,[],[f16])).
% 2.69/0.71  % SZS output end Proof for theBenchmark
% 2.69/0.71  % (8865)------------------------------
% 2.69/0.71  % (8865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.69/0.71  % (8865)Termination reason: Refutation
% 2.69/0.71  
% 2.69/0.71  % (8865)Memory used [KB]: 11513
% 2.69/0.71  % (8865)Time elapsed: 0.298 s
% 2.69/0.71  % (8865)------------------------------
% 2.69/0.71  % (8865)------------------------------
% 2.69/0.71  % (8838)Success in time 0.354 s
%------------------------------------------------------------------------------
