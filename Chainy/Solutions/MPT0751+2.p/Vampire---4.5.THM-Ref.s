%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0751+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:47 EST 2020

% Result     : Theorem 4.06s
% Output     : Refutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 193 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  382 ( 942 expanded)
%              Number of equality atoms :   63 ( 180 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5019,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1526,f1532,f1538,f1851,f1880,f1885,f1890,f4954])).

fof(f4954,plain,
    ( ~ spl39_1
    | spl39_23
    | ~ spl39_24
    | ~ spl39_25 ),
    inference(avatar_contradiction_clause,[],[f4953])).

fof(f4953,plain,
    ( $false
    | ~ spl39_1
    | spl39_23
    | ~ spl39_24
    | ~ spl39_25 ),
    inference(subsumption_resolution,[],[f4952,f1506])).

fof(f1506,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1505])).

fof(f1505,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f1441])).

fof(f1441,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1273])).

fof(f1273,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK24(X0,X1) != X0
            | ~ r2_hidden(sK24(X0,X1),X1) )
          & ( sK24(X0,X1) = X0
            | r2_hidden(sK24(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f1271,f1272])).

fof(f1272,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK24(X0,X1) != X0
          | ~ r2_hidden(sK24(X0,X1),X1) )
        & ( sK24(X0,X1) = X0
          | r2_hidden(sK24(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1271,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f1270])).

fof(f1270,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f4952,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl39_1
    | spl39_23
    | ~ spl39_24
    | ~ spl39_25 ),
    inference(forward_demodulation,[],[f4912,f4015])).

fof(f4015,plain,
    ( sK0 = sK3(sK0)
    | ~ spl39_1
    | spl39_23
    | ~ spl39_24
    | ~ spl39_25 ),
    inference(subsumption_resolution,[],[f4000,f2341])).

fof(f2341,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK3(sK0)))
    | ~ spl39_1
    | spl39_23
    | ~ spl39_25 ),
    inference(subsumption_resolution,[],[f2340,f1993])).

fof(f1993,plain,
    ( v3_ordinal1(k1_ordinal1(sK3(sK0)))
    | ~ spl39_25 ),
    inference(resolution,[],[f1889,f1316])).

fof(f1316,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1113])).

fof(f1113,plain,(
    ! [X0] :
      ( ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1068])).

fof(f1068,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(f1889,plain,
    ( v3_ordinal1(sK3(sK0))
    | ~ spl39_25 ),
    inference(avatar_component_clause,[],[f1887])).

fof(f1887,plain,
    ( spl39_25
  <=> v3_ordinal1(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_25])])).

fof(f2340,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK3(sK0)))
    | ~ v3_ordinal1(k1_ordinal1(sK3(sK0)))
    | ~ spl39_1
    | spl39_23
    | ~ spl39_25 ),
    inference(subsumption_resolution,[],[f2339,f1301])).

fof(f1301,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f1201])).

fof(f1201,plain,
    ( ( ( v4_ordinal1(sK0)
        & sK0 = k1_ordinal1(sK1)
        & v3_ordinal1(sK1) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK0
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK0) ) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1110,f1200,f1199])).

fof(f1199,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK0)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK0) ) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1200,plain,
    ( ? [X1] :
        ( k1_ordinal1(X1) = sK0
        & v3_ordinal1(X1) )
   => ( sK0 = k1_ordinal1(sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1110,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1106])).

fof(f1106,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f1101])).

fof(f1101,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f1100])).

fof(f1100,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

fof(f2339,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK3(sK0)))
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK3(sK0)))
    | ~ spl39_1
    | spl39_23
    | ~ spl39_25 ),
    inference(subsumption_resolution,[],[f2327,f2006])).

fof(f2006,plain,
    ( sK0 != k1_ordinal1(sK3(sK0))
    | ~ spl39_1
    | ~ spl39_25 ),
    inference(resolution,[],[f1889,f1521])).

fof(f1521,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | k1_ordinal1(X2) != sK0 )
    | ~ spl39_1 ),
    inference(avatar_component_clause,[],[f1520])).

fof(f1520,plain,
    ( spl39_1
  <=> ! [X2] :
        ( k1_ordinal1(X2) != sK0
        | ~ v3_ordinal1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_1])])).

fof(f2327,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK3(sK0)))
    | sK0 = k1_ordinal1(sK3(sK0))
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK3(sK0)))
    | spl39_23 ),
    inference(resolution,[],[f1879,f1344])).

fof(f1344,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1125])).

fof(f1125,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1124])).

fof(f1124,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1084])).

fof(f1084,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f1879,plain,
    ( ~ r2_hidden(k1_ordinal1(sK3(sK0)),sK0)
    | spl39_23 ),
    inference(avatar_component_clause,[],[f1877])).

fof(f1877,plain,
    ( spl39_23
  <=> r2_hidden(k1_ordinal1(sK3(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_23])])).

fof(f4000,plain,
    ( sK0 = sK3(sK0)
    | ~ r2_hidden(sK0,k1_ordinal1(sK3(sK0)))
    | ~ spl39_24 ),
    inference(resolution,[],[f2084,f1308])).

fof(f1308,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f1203])).

fof(f1203,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f1202])).

fof(f1202,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1078])).

fof(f1078,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f2084,plain,
    ( ~ r2_hidden(sK0,sK3(sK0))
    | ~ spl39_24 ),
    inference(resolution,[],[f1884,f1357])).

fof(f1357,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1134])).

fof(f1134,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f1884,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl39_24 ),
    inference(avatar_component_clause,[],[f1882])).

fof(f1882,plain,
    ( spl39_24
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_24])])).

fof(f4912,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK3(sK0)))
    | ~ spl39_24 ),
    inference(resolution,[],[f2090,f1351])).

fof(f1351,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1131])).

fof(f1131,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1105])).

fof(f1105,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f2090,plain,
    ( r1_tarski(k1_tarski(sK3(sK0)),sK0)
    | ~ spl39_24 ),
    inference(resolution,[],[f1884,f1431])).

fof(f1431,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1264])).

fof(f1264,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f302])).

fof(f302,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1890,plain,
    ( spl39_25
    | spl39_2 ),
    inference(avatar_split_clause,[],[f1547,f1523,f1887])).

fof(f1523,plain,
    ( spl39_2
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_2])])).

fof(f1547,plain,
    ( v4_ordinal1(sK0)
    | v3_ordinal1(sK3(sK0)) ),
    inference(resolution,[],[f1301,f1325])).

fof(f1325,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | v3_ordinal1(sK3(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1212])).

fof(f1212,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK3(X0)),X0)
            & r2_hidden(sK3(X0),X0)
            & v3_ordinal1(sK3(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f1210,f1211])).

fof(f1211,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK3(X0)),X0)
        & r2_hidden(sK3(X0),X0)
        & v3_ordinal1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1210,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f1209])).

fof(f1209,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f1116])).

fof(f1116,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1115])).

fof(f1115,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1099])).

fof(f1099,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f1885,plain,
    ( spl39_24
    | spl39_2 ),
    inference(avatar_split_clause,[],[f1548,f1523,f1882])).

fof(f1548,plain,
    ( v4_ordinal1(sK0)
    | r2_hidden(sK3(sK0),sK0) ),
    inference(resolution,[],[f1301,f1326])).

fof(f1326,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK3(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1212])).

fof(f1880,plain,
    ( ~ spl39_23
    | spl39_2 ),
    inference(avatar_split_clause,[],[f1549,f1523,f1877])).

fof(f1549,plain,
    ( v4_ordinal1(sK0)
    | ~ r2_hidden(k1_ordinal1(sK3(sK0)),sK0) ),
    inference(resolution,[],[f1301,f1327])).

fof(f1327,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK3(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1212])).

fof(f1851,plain,
    ( ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4 ),
    inference(avatar_split_clause,[],[f1850,f1534,f1528,f1523])).

fof(f1528,plain,
    ( spl39_3
  <=> sK0 = k1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_3])])).

fof(f1534,plain,
    ( spl39_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_4])])).

fof(f1850,plain,
    ( ~ v4_ordinal1(sK0)
    | ~ spl39_3
    | ~ spl39_4 ),
    inference(subsumption_resolution,[],[f1849,f1345])).

fof(f1345,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1126])).

fof(f1126,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1104])).

fof(f1104,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X5,X0)
        & r2_hidden(X4,X5)
        & r2_hidden(X3,X4)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_ordinal1)).

fof(f1849,plain,
    ( r2_hidden(sK0,sK0)
    | ~ v4_ordinal1(sK0)
    | ~ spl39_3
    | ~ spl39_4 ),
    inference(forward_demodulation,[],[f1848,f1530])).

fof(f1530,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ spl39_3 ),
    inference(avatar_component_clause,[],[f1528])).

fof(f1848,plain,
    ( r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0)
    | ~ spl39_3
    | ~ spl39_4 ),
    inference(subsumption_resolution,[],[f1834,f1301])).

fof(f1834,plain,
    ( r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl39_3
    | ~ spl39_4 ),
    inference(subsumption_resolution,[],[f1789,f1536])).

fof(f1536,plain,
    ( v3_ordinal1(sK1)
    | ~ spl39_4 ),
    inference(avatar_component_clause,[],[f1534])).

fof(f1789,plain,
    ( r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl39_3 ),
    inference(resolution,[],[f1614,f1324])).

fof(f1324,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1212])).

fof(f1614,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl39_3 ),
    inference(superposition,[],[f1319,f1530])).

fof(f1319,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f1076])).

fof(f1076,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f1538,plain,
    ( ~ spl39_2
    | spl39_4 ),
    inference(avatar_split_clause,[],[f1302,f1534,f1523])).

fof(f1302,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f1201])).

fof(f1532,plain,
    ( ~ spl39_2
    | spl39_3 ),
    inference(avatar_split_clause,[],[f1304,f1528,f1523])).

fof(f1304,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f1201])).

fof(f1526,plain,
    ( spl39_1
    | spl39_2 ),
    inference(avatar_split_clause,[],[f1307,f1523,f1520])).

fof(f1307,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f1201])).
%------------------------------------------------------------------------------
