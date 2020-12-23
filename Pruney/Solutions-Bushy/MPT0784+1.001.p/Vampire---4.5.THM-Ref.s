%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0784+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:39 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 731 expanded)
%              Number of leaves         :   33 ( 202 expanded)
%              Depth                    :   18
%              Number of atoms          :  811 (3300 expanded)
%              Number of equality atoms :  104 ( 470 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f792,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f138,f148,f158,f207,f215,f305,f313,f352,f383,f461,f477,f499,f517,f598,f618,f712,f777,f791])).

fof(f791,plain,
    ( ~ spl12_2
    | spl12_13
    | ~ spl12_15
    | ~ spl12_19 ),
    inference(avatar_contradiction_clause,[],[f790])).

fof(f790,plain,
    ( $false
    | ~ spl12_2
    | spl12_13
    | ~ spl12_15
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f539,f734])).

fof(f734,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f724,f96])).

fof(f96,plain,(
    ~ r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) ),
    inference(resolution,[],[f90,f55])).

fof(f55,plain,(
    ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f724,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl12_19 ),
    inference(superposition,[],[f86,f597])).

fof(f597,plain,
    ( sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f595])).

fof(f595,plain,
    ( spl12_19
  <=> sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f539,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl12_2
    | spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f538,f95])).

fof(f95,plain,(
    ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(resolution,[],[f89,f55])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f538,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_2
    | spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f529,f459])).

fof(f459,plain,
    ( sK0 != sK1
    | spl12_13 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl12_13
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f529,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | sK0 = sK1
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_2
    | ~ spl12_15 ),
    inference(superposition,[],[f160,f476])).

fof(f476,plain,
    ( sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl12_15
  <=> sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,sK11(k1_wellord1(sK2,X0),X1)))
        | sK11(k1_wellord1(sK2,X0),X1) = X0
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl12_2 ),
    inference(resolution,[],[f159,f86])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | X0 = X1
        | ~ r2_hidden(X1,k1_wellord1(sK2,X0)) )
    | ~ spl12_2 ),
    inference(resolution,[],[f139,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(X0,k1_wellord1(sK2,X1)) ) ),
    inference(resolution,[],[f92,f53])).

fof(f53,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
                | sK10(X0,X1,X2) = X1
                | ~ r2_hidden(sK10(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
                  & sK10(X0,X1,X2) != X1 )
                | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
          | sK10(X0,X1,X2) = X1
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
            & sK10(X0,X1,X2) != X1 )
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X0),sK2)
        | X0 = X1
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1)) )
    | ~ spl12_2 ),
    inference(resolution,[],[f129,f114])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) )
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl12_2
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f777,plain,
    ( ~ spl12_4
    | spl12_12
    | ~ spl12_19 ),
    inference(avatar_contradiction_clause,[],[f776])).

fof(f776,plain,
    ( $false
    | ~ spl12_4
    | spl12_12
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f774,f455])).

fof(f455,plain,
    ( ~ r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | spl12_12 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl12_12
  <=> r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f774,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | ~ spl12_4
    | ~ spl12_19 ),
    inference(resolution,[],[f728,f95])).

fof(f728,plain,
    ( ! [X1] :
        ( r1_tarski(k1_wellord1(sK2,sK0),X1)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),X1),sK1),sK2) )
    | ~ spl12_4
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f718,f96])).

fof(f718,plain,
    ( ! [X1] :
        ( r1_tarski(k1_wellord1(sK2,sK0),X1)
        | r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),X1),sK1),sK2) )
    | ~ spl12_4
    | ~ spl12_19 ),
    inference(superposition,[],[f164,f597])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,sK11(k1_wellord1(sK2,X0),X1)),X2)
        | r1_tarski(k1_wellord1(sK2,X0),X1)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK11(k1_wellord1(sK2,X0),X1)),X2),X0),sK2) )
    | ~ spl12_4 ),
    inference(resolution,[],[f163,f86])).

fof(f163,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,sK11(k1_wellord1(sK2,X1),X2)))
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | r1_tarski(k1_wellord1(sK2,X1),X2) )
    | ~ spl12_4 ),
    inference(resolution,[],[f162,f86])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k1_wellord1(sK2,X1))
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X0,k1_wellord1(sK2,X2)) )
    | ~ spl12_4 ),
    inference(resolution,[],[f161,f114])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X2),sK2)
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X2,k1_wellord1(sK2,X1)) )
    | ~ spl12_4 ),
    inference(resolution,[],[f147,f114])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) )
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl12_4
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f712,plain,(
    ~ spl12_18 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f703,f96])).

fof(f703,plain,
    ( r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl12_18 ),
    inference(resolution,[],[f593,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f593,plain,
    ( r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0))
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f591])).

fof(f591,plain,
    ( spl12_18
  <=> r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f618,plain,
    ( spl12_18
    | spl12_19
    | ~ spl12_11 ),
    inference(avatar_split_clause,[],[f611,f450,f595,f591])).

fof(f450,plain,
    ( spl12_11
  <=> r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f611,plain,
    ( sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0))
    | ~ spl12_11 ),
    inference(resolution,[],[f452,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | X0 = X1
      | r2_hidden(X0,k1_wellord1(sK2,X1)) ) ),
    inference(resolution,[],[f91,f53])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f452,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f450])).

fof(f598,plain,
    ( spl12_18
    | spl12_19
    | ~ spl12_4
    | ~ spl12_15 ),
    inference(avatar_split_clause,[],[f583,f474,f146,f595,f591])).

fof(f583,plain,
    ( sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0))
    | ~ spl12_4
    | ~ spl12_15 ),
    inference(resolution,[],[f581,f118])).

fof(f581,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)
    | ~ spl12_4
    | ~ spl12_15 ),
    inference(resolution,[],[f541,f96])).

fof(f541,plain,
    ( ! [X1] :
        ( r1_tarski(k1_wellord1(sK2,sK1),X1)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),X1),sK0),sK2) )
    | ~ spl12_4
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f531,f95])).

fof(f531,plain,
    ( ! [X1] :
        ( r1_tarski(k1_wellord1(sK2,sK1),X1)
        | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),X1),sK0),sK2) )
    | ~ spl12_4
    | ~ spl12_15 ),
    inference(superposition,[],[f164,f476])).

fof(f517,plain,(
    ~ spl12_13 ),
    inference(avatar_contradiction_clause,[],[f516])).

fof(f516,plain,
    ( $false
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f504,f98])).

fof(f98,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f87,f86])).

fof(f504,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | ~ spl12_13 ),
    inference(backward_demodulation,[],[f96,f460])).

fof(f460,plain,
    ( sK0 = sK1
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f458])).

fof(f499,plain,(
    ~ spl12_14 ),
    inference(avatar_contradiction_clause,[],[f498])).

fof(f498,plain,
    ( $false
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f490,f95])).

fof(f490,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_14 ),
    inference(resolution,[],[f472,f87])).

fof(f472,plain,
    ( r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl12_14
  <=> r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f477,plain,
    ( spl12_14
    | spl12_15
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f462,f454,f474,f470])).

fof(f462,plain,
    ( sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl12_12 ),
    inference(resolution,[],[f456,f118])).

fof(f456,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f454])).

fof(f461,plain,
    ( spl12_11
    | spl12_12
    | spl12_13
    | ~ spl12_2
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_10 ),
    inference(avatar_split_clause,[],[f448,f311,f307,f303,f299,f128,f458,f454,f450])).

fof(f299,plain,
    ( spl12_7
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f303,plain,
    ( spl12_8
  <=> ! [X0] :
        ( sK0 = X0
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,sK0),sK2)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f307,plain,
    ( spl12_9
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f311,plain,
    ( spl12_10
  <=> ! [X1] :
        ( sK1 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,sK1),sK2)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f448,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)
    | ~ spl12_2
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f447,f300])).

fof(f300,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f299])).

fof(f447,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)
    | ~ spl12_2
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f443,f308])).

fof(f308,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f307])).

fof(f443,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)
    | ~ spl12_2
    | ~ spl12_8
    | ~ spl12_10 ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | sK0 = sK1
    | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)
    | ~ spl12_2
    | ~ spl12_8
    | ~ spl12_10 ),
    inference(resolution,[],[f398,f312])).

fof(f312,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | sK1 = X1
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X1),sK2) )
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f311])).

fof(f398,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(sK0,X1),sK2)
        | sK0 = X1
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2)) )
    | ~ spl12_2
    | ~ spl12_8 ),
    inference(duplicate_literal_removal,[],[f391])).

fof(f391,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | sK0 = X1
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X1),sK2)
        | sK0 = X1
        | ~ r2_hidden(k4_tarski(sK0,X1),sK2) )
    | ~ spl12_2
    | ~ spl12_8 ),
    inference(resolution,[],[f304,f129])).

fof(f304,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | sK0 = X0
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X0),sK2) )
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f303])).

fof(f383,plain,(
    spl12_9 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl12_9 ),
    inference(subsumption_resolution,[],[f380,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f380,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_wellord1(sK2,sK0))
    | spl12_9 ),
    inference(resolution,[],[f358,f90])).

fof(f358,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_xboole_0)
    | spl12_9 ),
    inference(backward_demodulation,[],[f55,f322])).

fof(f322,plain,
    ( k1_xboole_0 = k1_wellord1(sK2,sK1)
    | spl12_9 ),
    inference(resolution,[],[f309,f106])).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_relat_1(sK2))
      | k1_xboole_0 = k1_wellord1(sK2,X0) ) ),
    inference(resolution,[],[f84,f53])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(X0,k3_relat_1(X1))
      | k1_wellord1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k1_xboole_0
      | r2_hidden(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k1_xboole_0
      | r2_hidden(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord1(X1,X0) = k1_xboole_0
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

fof(f309,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | spl12_9 ),
    inference(avatar_component_clause,[],[f307])).

fof(f352,plain,(
    spl12_7 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | spl12_7 ),
    inference(subsumption_resolution,[],[f331,f56])).

fof(f331,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_wellord1(sK2,sK1))
    | spl12_7 ),
    inference(backward_demodulation,[],[f95,f314])).

fof(f314,plain,
    ( k1_xboole_0 = k1_wellord1(sK2,sK0)
    | spl12_7 ),
    inference(resolution,[],[f301,f106])).

fof(f301,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | spl12_7 ),
    inference(avatar_component_clause,[],[f299])).

fof(f313,plain,
    ( ~ spl12_9
    | spl12_10
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f296,f205,f146,f311,f307])).

fof(f205,plain,
    ( spl12_6
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f296,plain,
    ( ! [X1] :
        ( sK1 = X1
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X1),sK2)
        | r2_hidden(k4_tarski(X1,sK1),sK2)
        | ~ r2_hidden(sK1,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2)) )
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(resolution,[],[f286,f96])).

fof(f286,plain,
    ( ! [X6,X8,X7] :
        ( r1_tarski(k1_wellord1(sK2,X7),X8)
        | X6 = X7
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X7),X8),X6),sK2)
        | r2_hidden(k4_tarski(X6,X7),sK2)
        | ~ r2_hidden(X7,k3_relat_1(sK2))
        | ~ r2_hidden(X6,k3_relat_1(sK2)) )
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(resolution,[],[f266,f86])).

fof(f266,plain,
    ( ! [X6,X8,X7] :
        ( ~ r2_hidden(X8,k1_wellord1(sK2,X6))
        | ~ r2_hidden(X7,k3_relat_1(sK2))
        | X6 = X7
        | r2_hidden(k4_tarski(X8,X7),sK2)
        | r2_hidden(k4_tarski(X7,X6),sK2)
        | ~ r2_hidden(X6,k3_relat_1(sK2)) )
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(resolution,[],[f217,f114])).

fof(f217,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(k4_tarski(X5,X4),sK2)
        | ~ r2_hidden(X4,k3_relat_1(sK2))
        | ~ r2_hidden(X3,k3_relat_1(sK2))
        | X3 = X4
        | r2_hidden(k4_tarski(X5,X3),sK2)
        | r2_hidden(k4_tarski(X3,X4),sK2) )
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(resolution,[],[f206,f147])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f205])).

fof(f305,plain,
    ( ~ spl12_7
    | spl12_8
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f295,f205,f146,f303,f299])).

fof(f295,plain,
    ( ! [X0] :
        ( sK0 = X0
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X0),sK2)
        | r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ r2_hidden(sK0,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2)) )
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(resolution,[],[f286,f95])).

fof(f215,plain,(
    spl12_5 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl12_5 ),
    inference(subsumption_resolution,[],[f213,f53])).

fof(f213,plain,
    ( ~ v1_relat_1(sK2)
    | spl12_5 ),
    inference(subsumption_resolution,[],[f210,f54])).

fof(f54,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f210,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl12_5 ),
    inference(resolution,[],[f203,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f203,plain,
    ( ~ v6_relat_2(sK2)
    | spl12_5 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl12_5
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f207,plain,
    ( ~ spl12_5
    | spl12_6 ),
    inference(avatar_split_clause,[],[f199,f205,f201])).

fof(f199,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK2)
      | X0 = X1
      | ~ r2_hidden(X1,k3_relat_1(sK2))
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | ~ v6_relat_2(sK2)
      | r2_hidden(k4_tarski(X1,X0),sK2) ) ),
    inference(resolution,[],[f61,f53])).

fof(f61,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)
            & sK5(X0) != sK6(X0)
            & r2_hidden(sK6(X0),k3_relat_1(X0))
            & r2_hidden(sK5(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)
        & sK5(X0) != sK6(X0)
        & r2_hidden(sK6(X0),k3_relat_1(X0))
        & r2_hidden(sK5(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f158,plain,(
    spl12_3 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl12_3 ),
    inference(subsumption_resolution,[],[f156,f53])).

fof(f156,plain,
    ( ~ v1_relat_1(sK2)
    | spl12_3 ),
    inference(subsumption_resolution,[],[f152,f54])).

fof(f152,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl12_3 ),
    inference(resolution,[],[f144,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f144,plain,
    ( ~ v8_relat_2(sK2)
    | spl12_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl12_3
  <=> v8_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f148,plain,
    ( ~ spl12_3
    | spl12_4 ),
    inference(avatar_split_clause,[],[f140,f146,f142])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(k4_tarski(X2,X0),sK2)
      | ~ v8_relat_2(sK2)
      | r2_hidden(k4_tarski(X2,X1),sK2) ) ),
    inference(resolution,[],[f67,f53])).

fof(f67,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X6),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0)
            & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
            & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0)
        & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
        & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

fof(f138,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl12_1 ),
    inference(subsumption_resolution,[],[f136,f53])).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f133,f54])).

fof(f133,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl12_1 ),
    inference(resolution,[],[f126,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f126,plain,
    ( ~ v4_relat_2(sK2)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl12_1
  <=> v4_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f130,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f122,f128,f124])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(k4_tarski(X1,X0),sK2)
      | ~ v4_relat_2(sK2)
      | X0 = X1 ) ),
    inference(resolution,[],[f57,f53])).

fof(f57,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | X3 = X4 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK3(X0) != sK4(X0)
            & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK3(X0) != sK4(X0)
        & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_wellord1)).

%------------------------------------------------------------------------------
