%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0720+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:46 EST 2020

% Result     : Theorem 12.18s
% Output     : Refutation 12.56s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 134 expanded)
%              Number of leaves         :   19 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  293 ( 605 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19845,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2461,f2466,f2471,f2476,f2481,f2491,f2813,f15792,f15797,f19833])).

fof(f19833,plain,
    ( ~ spl124_1
    | ~ spl124_2
    | ~ spl124_3
    | ~ spl124_4
    | ~ spl124_5
    | ~ spl124_24
    | ~ spl124_66
    | spl124_67 ),
    inference(avatar_contradiction_clause,[],[f19832])).

fof(f19832,plain,
    ( $false
    | ~ spl124_1
    | ~ spl124_2
    | ~ spl124_3
    | ~ spl124_4
    | ~ spl124_5
    | ~ spl124_24
    | ~ spl124_66
    | spl124_67 ),
    inference(subsumption_resolution,[],[f15878,f16403])).

fof(f16403,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl124_24 ),
    inference(unit_resulting_resolution,[],[f2812,f2283])).

fof(f2283,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1415])).

fof(f1415,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f2812,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl124_24 ),
    inference(avatar_component_clause,[],[f2810])).

fof(f2810,plain,
    ( spl124_24
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_24])])).

fof(f15878,plain,
    ( r2_hidden(k1_funct_1(sK1,sK28(k1_relat_1(sK1),k1_relat_1(sK0))),k1_xboole_0)
    | ~ spl124_1
    | ~ spl124_2
    | ~ spl124_3
    | ~ spl124_4
    | ~ spl124_5
    | ~ spl124_66
    | spl124_67 ),
    inference(backward_demodulation,[],[f15803,f15867])).

fof(f15867,plain,
    ( k1_xboole_0 = k1_funct_1(sK0,sK28(k1_relat_1(sK1),k1_relat_1(sK0)))
    | ~ spl124_1
    | ~ spl124_2
    | spl124_67 ),
    inference(unit_resulting_resolution,[],[f2460,f2465,f15796,f2331])).

fof(f2331,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1814])).

fof(f1814,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1489])).

fof(f1489,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1122])).

fof(f1122,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1121])).

fof(f1121,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f903])).

fof(f903,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f15796,plain,
    ( ~ r2_hidden(sK28(k1_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0))
    | spl124_67 ),
    inference(avatar_component_clause,[],[f15794])).

fof(f15794,plain,
    ( spl124_67
  <=> r2_hidden(sK28(k1_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_67])])).

fof(f2465,plain,
    ( v1_funct_1(sK0)
    | ~ spl124_2 ),
    inference(avatar_component_clause,[],[f2463])).

fof(f2463,plain,
    ( spl124_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_2])])).

fof(f2460,plain,
    ( v1_relat_1(sK0)
    | ~ spl124_1 ),
    inference(avatar_component_clause,[],[f2458])).

fof(f2458,plain,
    ( spl124_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_1])])).

fof(f15803,plain,
    ( r2_hidden(k1_funct_1(sK1,sK28(k1_relat_1(sK1),k1_relat_1(sK0))),k1_funct_1(sK0,sK28(k1_relat_1(sK1),k1_relat_1(sK0))))
    | ~ spl124_1
    | ~ spl124_2
    | ~ spl124_3
    | ~ spl124_4
    | ~ spl124_5
    | ~ spl124_66 ),
    inference(unit_resulting_resolution,[],[f2460,f2465,f2470,f2475,f2480,f15791,f1719])).

fof(f1719,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ v5_funct_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1447])).

fof(f1447,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK2(X0,X1)),k1_funct_1(X0,sK2(X0,X1)))
                & r2_hidden(sK2(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f1445,f1446])).

fof(f1446,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK2(X0,X1)),k1_funct_1(X0,sK2(X0,X1)))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1445,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1444])).

fof(f1444,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1063])).

fof(f1063,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1062])).

fof(f1062,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f902])).

fof(f902,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f15791,plain,
    ( r2_hidden(sK28(k1_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK1))
    | ~ spl124_66 ),
    inference(avatar_component_clause,[],[f15789])).

fof(f15789,plain,
    ( spl124_66
  <=> r2_hidden(sK28(k1_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_66])])).

fof(f2480,plain,
    ( v5_funct_1(sK1,sK0)
    | ~ spl124_5 ),
    inference(avatar_component_clause,[],[f2478])).

fof(f2478,plain,
    ( spl124_5
  <=> v5_funct_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_5])])).

fof(f2475,plain,
    ( v1_funct_1(sK1)
    | ~ spl124_4 ),
    inference(avatar_component_clause,[],[f2473])).

fof(f2473,plain,
    ( spl124_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_4])])).

fof(f2470,plain,
    ( v1_relat_1(sK1)
    | ~ spl124_3 ),
    inference(avatar_component_clause,[],[f2468])).

fof(f2468,plain,
    ( spl124_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_3])])).

fof(f15797,plain,
    ( ~ spl124_67
    | spl124_7 ),
    inference(avatar_split_clause,[],[f3298,f2488,f15794])).

fof(f2488,plain,
    ( spl124_7
  <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl124_7])])).

fof(f3298,plain,
    ( ~ r2_hidden(sK28(k1_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0))
    | spl124_7 ),
    inference(unit_resulting_resolution,[],[f2490,f1838])).

fof(f1838,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK28(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1514])).

fof(f1514,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK28(X0,X1),X1)
          & r2_hidden(sK28(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28])],[f1512,f1513])).

fof(f1513,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK28(X0,X1),X1)
        & r2_hidden(sK28(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1512,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1511])).

fof(f1511,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1134])).

fof(f1134,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2490,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK0))
    | spl124_7 ),
    inference(avatar_component_clause,[],[f2488])).

fof(f15792,plain,
    ( spl124_66
    | spl124_7 ),
    inference(avatar_split_clause,[],[f3296,f2488,f15789])).

fof(f3296,plain,
    ( r2_hidden(sK28(k1_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK1))
    | spl124_7 ),
    inference(unit_resulting_resolution,[],[f2490,f1837])).

fof(f1837,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK28(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1514])).

fof(f2813,plain,(
    spl124_24 ),
    inference(avatar_split_clause,[],[f2314,f2810])).

fof(f2314,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f2491,plain,(
    ~ spl124_7 ),
    inference(avatar_split_clause,[],[f1713,f2488])).

fof(f1713,plain,(
    ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f1441])).

fof(f1441,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK0))
    & v5_funct_1(sK1,sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1058,f1440,f1439])).

fof(f1439,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X0))
            & v5_funct_1(X1,X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(X1),k1_relat_1(sK0))
          & v5_funct_1(X1,sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1440,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(X1),k1_relat_1(sK0))
        & v5_funct_1(X1,sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK0))
      & v5_funct_1(sK1,sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1058,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X0))
          & v5_funct_1(X1,X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1057])).

fof(f1057,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X0))
          & v5_funct_1(X1,X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f998])).

fof(f998,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v5_funct_1(X1,X0)
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
           => r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f997])).

fof(f997,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v5_funct_1(X1,X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
         => r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_1)).

fof(f2481,plain,(
    spl124_5 ),
    inference(avatar_split_clause,[],[f1712,f2478])).

fof(f1712,plain,(
    v5_funct_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f1441])).

fof(f2476,plain,(
    spl124_4 ),
    inference(avatar_split_clause,[],[f1711,f2473])).

fof(f1711,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1441])).

fof(f2471,plain,(
    spl124_3 ),
    inference(avatar_split_clause,[],[f1710,f2468])).

fof(f1710,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1441])).

fof(f2466,plain,(
    spl124_2 ),
    inference(avatar_split_clause,[],[f1709,f2463])).

fof(f1709,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1441])).

fof(f2461,plain,(
    spl124_1 ),
    inference(avatar_split_clause,[],[f1708,f2458])).

fof(f1708,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1441])).
%------------------------------------------------------------------------------
