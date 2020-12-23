%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0638+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:41 EST 2020

% Result     : Theorem 26.08s
% Output     : Refutation 26.08s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 235 expanded)
%              Number of leaves         :   18 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :  452 (1381 expanded)
%              Number of equality atoms :  141 ( 541 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26657,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1494,f1499,f1504,f1509,f1781,f2868,f5768,f25110,f26632])).

fof(f26632,plain,
    ( ~ spl36_1
    | ~ spl36_2
    | ~ spl36_3
    | ~ spl36_4
    | ~ spl36_6
    | ~ spl36_39
    | spl36_60
    | ~ spl36_125 ),
    inference(avatar_contradiction_clause,[],[f26631])).

fof(f26631,plain,
    ( $false
    | ~ spl36_1
    | ~ spl36_2
    | ~ spl36_3
    | ~ spl36_4
    | ~ spl36_6
    | ~ spl36_39
    | spl36_60
    | ~ spl36_125 ),
    inference(subsumption_resolution,[],[f26630,f5767])).

fof(f5767,plain,
    ( sK2(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))
    | spl36_60 ),
    inference(avatar_component_clause,[],[f5765])).

fof(f5765,plain,
    ( spl36_60
  <=> sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_60])])).

fof(f26630,plain,
    ( sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))
    | ~ spl36_1
    | ~ spl36_2
    | ~ spl36_3
    | ~ spl36_4
    | ~ spl36_6
    | ~ spl36_39
    | ~ spl36_125 ),
    inference(forward_demodulation,[],[f26612,f3049])).

fof(f3049,plain,
    ( sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK34(sK0,sK2(k2_relat_1(sK0),sK1)))
    | ~ spl36_1
    | ~ spl36_2
    | ~ spl36_39 ),
    inference(subsumption_resolution,[],[f3048,f1493])).

fof(f1493,plain,
    ( v1_relat_1(sK0)
    | ~ spl36_1 ),
    inference(avatar_component_clause,[],[f1491])).

fof(f1491,plain,
    ( spl36_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_1])])).

fof(f3048,plain,
    ( sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK34(sK0,sK2(k2_relat_1(sK0),sK1)))
    | ~ v1_relat_1(sK0)
    | ~ spl36_2
    | ~ spl36_39 ),
    inference(subsumption_resolution,[],[f3036,f1498])).

fof(f1498,plain,
    ( v1_funct_1(sK0)
    | ~ spl36_2 ),
    inference(avatar_component_clause,[],[f1496])).

fof(f1496,plain,
    ( spl36_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_2])])).

fof(f3036,plain,
    ( sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK34(sK0,sK2(k2_relat_1(sK0),sK1)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl36_39 ),
    inference(resolution,[],[f2867,f1487])).

fof(f1487,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK34(X0,X5)) = X5
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1444])).

fof(f1444,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK34(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1205])).

fof(f1205,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK32(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK32(X0,X1),X1) )
              & ( ( sK32(X0,X1) = k1_funct_1(X0,sK33(X0,X1))
                  & r2_hidden(sK33(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK32(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK34(X0,X5)) = X5
                    & r2_hidden(sK34(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK32,sK33,sK34])],[f1201,f1204,f1203,f1202])).

fof(f1202,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK32(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK32(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK32(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK32(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1203,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK32(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK32(X0,X1) = k1_funct_1(X0,sK33(X0,X1))
        & r2_hidden(sK33(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1204,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK34(X0,X5)) = X5
        & r2_hidden(sK34(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1201,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1200])).

fof(f1200,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1106])).

fof(f1106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1105])).

fof(f1105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f891])).

fof(f891,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f2867,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl36_39 ),
    inference(avatar_component_clause,[],[f2865])).

fof(f2865,plain,
    ( spl36_39
  <=> r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_39])])).

fof(f26612,plain,
    ( k1_funct_1(sK0,sK34(sK0,sK2(k2_relat_1(sK0),sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK34(sK0,sK2(k2_relat_1(sK0),sK1))))
    | ~ spl36_1
    | ~ spl36_2
    | ~ spl36_3
    | ~ spl36_4
    | ~ spl36_6
    | ~ spl36_125 ),
    inference(resolution,[],[f25109,f1866])).

fof(f1866,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK0))
        | k1_funct_1(sK0,X5) = k1_funct_1(sK1,k1_funct_1(sK0,X5)) )
    | ~ spl36_1
    | ~ spl36_2
    | ~ spl36_3
    | ~ spl36_4
    | ~ spl36_6 ),
    inference(subsumption_resolution,[],[f1865,f1503])).

fof(f1503,plain,
    ( v1_relat_1(sK1)
    | ~ spl36_3 ),
    inference(avatar_component_clause,[],[f1501])).

fof(f1501,plain,
    ( spl36_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_3])])).

fof(f1865,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK0))
        | k1_funct_1(sK0,X5) = k1_funct_1(sK1,k1_funct_1(sK0,X5))
        | ~ v1_relat_1(sK1) )
    | ~ spl36_1
    | ~ spl36_2
    | ~ spl36_4
    | ~ spl36_6 ),
    inference(subsumption_resolution,[],[f1864,f1508])).

fof(f1508,plain,
    ( v1_funct_1(sK1)
    | ~ spl36_4 ),
    inference(avatar_component_clause,[],[f1506])).

fof(f1506,plain,
    ( spl36_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_4])])).

fof(f1864,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK0))
        | k1_funct_1(sK0,X5) = k1_funct_1(sK1,k1_funct_1(sK0,X5))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl36_1
    | ~ spl36_2
    | ~ spl36_6 ),
    inference(subsumption_resolution,[],[f1863,f1493])).

fof(f1863,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK0))
        | k1_funct_1(sK0,X5) = k1_funct_1(sK1,k1_funct_1(sK0,X5))
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl36_2
    | ~ spl36_6 ),
    inference(subsumption_resolution,[],[f1850,f1498])).

fof(f1850,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK0))
        | k1_funct_1(sK0,X5) = k1_funct_1(sK1,k1_funct_1(sK0,X5))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl36_6 ),
    inference(superposition,[],[f1263,f1780])).

fof(f1780,plain,
    ( sK0 = k5_relat_1(sK0,sK1)
    | ~ spl36_6 ),
    inference(avatar_component_clause,[],[f1778])).

fof(f1778,plain,
    ( spl36_6
  <=> sK0 = k5_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_6])])).

fof(f1263,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f965])).

fof(f965,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f964])).

fof(f964,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f917])).

fof(f917,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f25109,plain,
    ( r2_hidden(sK34(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ spl36_125 ),
    inference(avatar_component_clause,[],[f25107])).

fof(f25107,plain,
    ( spl36_125
  <=> r2_hidden(sK34(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_125])])).

fof(f25110,plain,
    ( spl36_125
    | ~ spl36_1
    | ~ spl36_2
    | ~ spl36_39 ),
    inference(avatar_split_clause,[],[f3047,f2865,f1496,f1491,f25107])).

fof(f3047,plain,
    ( r2_hidden(sK34(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ spl36_1
    | ~ spl36_2
    | ~ spl36_39 ),
    inference(subsumption_resolution,[],[f3046,f1493])).

fof(f3046,plain,
    ( r2_hidden(sK34(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl36_2
    | ~ spl36_39 ),
    inference(subsumption_resolution,[],[f3035,f1498])).

fof(f3035,plain,
    ( r2_hidden(sK34(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl36_39 ),
    inference(resolution,[],[f2867,f1488])).

fof(f1488,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK34(X0,X5),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1443])).

fof(f1443,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK34(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1205])).

fof(f5768,plain,
    ( ~ spl36_60
    | ~ spl36_3
    | ~ spl36_4 ),
    inference(avatar_split_clause,[],[f1763,f1506,f1501,f5765])).

fof(f1763,plain,
    ( sK2(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))
    | ~ spl36_3
    | ~ spl36_4 ),
    inference(subsumption_resolution,[],[f1762,f1489])).

fof(f1489,plain,(
    sK1 != k6_relat_1(k2_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f1214,f1212])).

fof(f1212,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1117])).

fof(f1117,plain,
    ( sK1 != k6_relat_1(k1_relat_1(sK1))
    & sK0 = k5_relat_1(sK0,sK1)
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f934,f1116,f1115])).

fof(f1115,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X1)) != X1
            & k5_relat_1(X0,X1) = X0
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & sK0 = k5_relat_1(sK0,X1)
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1116,plain,
    ( ? [X1] :
        ( k6_relat_1(k1_relat_1(X1)) != X1
        & sK0 = k5_relat_1(sK0,X1)
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK1 != k6_relat_1(k1_relat_1(sK1))
      & sK0 = k5_relat_1(sK0,sK1)
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f934,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f933])).

fof(f933,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f929])).

fof(f929,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f928])).

fof(f928,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f1214,plain,(
    sK1 != k6_relat_1(k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f1117])).

fof(f1762,plain,
    ( sK1 = k6_relat_1(k2_relat_1(sK0))
    | sK2(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))
    | ~ spl36_3
    | ~ spl36_4 ),
    inference(forward_demodulation,[],[f1761,f1212])).

fof(f1761,plain,
    ( sK2(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl36_3
    | ~ spl36_4 ),
    inference(forward_demodulation,[],[f1760,f1212])).

fof(f1760,plain,
    ( sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl36_3
    | ~ spl36_4 ),
    inference(subsumption_resolution,[],[f1727,f1503])).

fof(f1727,plain,
    ( sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl36_4 ),
    inference(resolution,[],[f1508,f1456])).

fof(f1456,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f1228])).

fof(f1228,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1128])).

fof(f1128,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f1126,f1127])).

fof(f1127,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1126,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f1125])).

fof(f1125,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1124])).

fof(f1124,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f942])).

fof(f942,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f941])).

fof(f941,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f922])).

fof(f922,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f2868,plain,
    ( spl36_39
    | ~ spl36_3
    | ~ spl36_4 ),
    inference(avatar_split_clause,[],[f1767,f1506,f1501,f2865])).

fof(f1767,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl36_3
    | ~ spl36_4 ),
    inference(subsumption_resolution,[],[f1766,f1489])).

fof(f1766,plain,
    ( sK1 = k6_relat_1(k2_relat_1(sK0))
    | r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl36_3
    | ~ spl36_4 ),
    inference(forward_demodulation,[],[f1765,f1212])).

fof(f1765,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl36_3
    | ~ spl36_4 ),
    inference(forward_demodulation,[],[f1764,f1212])).

fof(f1764,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl36_3
    | ~ spl36_4 ),
    inference(subsumption_resolution,[],[f1728,f1503])).

fof(f1728,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl36_4 ),
    inference(resolution,[],[f1508,f1457])).

fof(f1457,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f1227])).

fof(f1227,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1128])).

fof(f1781,plain,(
    spl36_6 ),
    inference(avatar_split_clause,[],[f1213,f1778])).

fof(f1213,plain,(
    sK0 = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f1117])).

fof(f1509,plain,(
    spl36_4 ),
    inference(avatar_split_clause,[],[f1211,f1506])).

fof(f1211,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1117])).

fof(f1504,plain,(
    spl36_3 ),
    inference(avatar_split_clause,[],[f1210,f1501])).

fof(f1210,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1117])).

fof(f1499,plain,(
    spl36_2 ),
    inference(avatar_split_clause,[],[f1209,f1496])).

fof(f1209,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1117])).

fof(f1494,plain,(
    spl36_1 ),
    inference(avatar_split_clause,[],[f1208,f1491])).

fof(f1208,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1117])).
%------------------------------------------------------------------------------
