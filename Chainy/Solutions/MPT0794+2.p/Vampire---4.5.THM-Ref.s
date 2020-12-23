%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0794+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 11.92s
% Output     : Refutation 11.92s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 286 expanded)
%              Number of leaves         :   21 ( 117 expanded)
%              Depth                    :   16
%              Number of atoms          :  623 (2047 expanded)
%              Number of equality atoms :   77 ( 340 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7033,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2194,f2199,f2204,f2209,f2350,f2355,f2389,f2394,f2474,f2630,f2635,f7018,f7031])).

fof(f7031,plain,
    ( ~ spl121_3
    | ~ spl121_4
    | spl121_5
    | ~ spl121_8
    | ~ spl121_10
    | ~ spl121_14
    | ~ spl121_15 ),
    inference(avatar_contradiction_clause,[],[f7030])).

fof(f7030,plain,
    ( $false
    | ~ spl121_3
    | ~ spl121_4
    | spl121_5
    | ~ spl121_8
    | ~ spl121_10
    | ~ spl121_14
    | ~ spl121_15 ),
    inference(subsumption_resolution,[],[f7029,f2349])).

fof(f2349,plain,
    ( sK3 != sK4
    | spl121_5 ),
    inference(avatar_component_clause,[],[f2347])).

fof(f2347,plain,
    ( spl121_5
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_5])])).

fof(f7029,plain,
    ( sK3 = sK4
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_8
    | ~ spl121_10
    | ~ spl121_14
    | ~ spl121_15 ),
    inference(forward_demodulation,[],[f7021,f2858])).

fof(f2858,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_8
    | ~ spl121_14 ),
    inference(subsumption_resolution,[],[f2857,f2203])).

fof(f2203,plain,
    ( v1_relat_1(sK2)
    | ~ spl121_3 ),
    inference(avatar_component_clause,[],[f2201])).

fof(f2201,plain,
    ( spl121_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_3])])).

fof(f2857,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ v1_relat_1(sK2)
    | ~ spl121_4
    | ~ spl121_8
    | ~ spl121_14 ),
    inference(subsumption_resolution,[],[f2856,f2208])).

fof(f2208,plain,
    ( v1_funct_1(sK2)
    | ~ spl121_4 ),
    inference(avatar_component_clause,[],[f2206])).

fof(f2206,plain,
    ( spl121_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_4])])).

fof(f2856,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl121_8
    | ~ spl121_14 ),
    inference(subsumption_resolution,[],[f2800,f2393])).

fof(f2393,plain,
    ( v2_funct_1(sK2)
    | ~ spl121_8 ),
    inference(avatar_component_clause,[],[f2391])).

fof(f2391,plain,
    ( spl121_8
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_8])])).

fof(f2800,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl121_14 ),
    inference(resolution,[],[f2629,f1726])).

fof(f1726,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1232])).

fof(f1232,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1231])).

fof(f1231,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1027])).

fof(f1027,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f2629,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl121_14 ),
    inference(avatar_component_clause,[],[f2627])).

fof(f2627,plain,
    ( spl121_14
  <=> r2_hidden(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_14])])).

fof(f7021,plain,
    ( sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_8
    | ~ spl121_10
    | ~ spl121_15 ),
    inference(backward_demodulation,[],[f2938,f2473])).

fof(f2473,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ spl121_10 ),
    inference(avatar_component_clause,[],[f2471])).

fof(f2471,plain,
    ( spl121_10
  <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_10])])).

fof(f2938,plain,
    ( sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4))
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_8
    | ~ spl121_15 ),
    inference(subsumption_resolution,[],[f2937,f2203])).

fof(f2937,plain,
    ( sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4))
    | ~ v1_relat_1(sK2)
    | ~ spl121_4
    | ~ spl121_8
    | ~ spl121_15 ),
    inference(subsumption_resolution,[],[f2936,f2208])).

fof(f2936,plain,
    ( sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl121_8
    | ~ spl121_15 ),
    inference(subsumption_resolution,[],[f2880,f2393])).

fof(f2880,plain,
    ( sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl121_15 ),
    inference(resolution,[],[f2634,f1726])).

fof(f2634,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl121_15 ),
    inference(avatar_component_clause,[],[f2632])).

fof(f2632,plain,
    ( spl121_15
  <=> r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_15])])).

fof(f7018,plain,
    ( ~ spl121_1
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6
    | ~ spl121_7
    | spl121_9 ),
    inference(avatar_contradiction_clause,[],[f7017])).

fof(f7017,plain,
    ( $false
    | ~ spl121_1
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6
    | ~ spl121_7
    | spl121_9 ),
    inference(subsumption_resolution,[],[f2469,f7001])).

fof(f7001,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)
    | ~ spl121_1
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6
    | ~ spl121_7 ),
    inference(resolution,[],[f2378,f2388])).

fof(f2388,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK0)
    | ~ spl121_7 ),
    inference(avatar_component_clause,[],[f2386])).

fof(f2386,plain,
    ( spl121_7
  <=> r2_hidden(k4_tarski(sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_7])])).

fof(f2378,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,X5),sK0)
        | r2_hidden(k4_tarski(k1_funct_1(sK2,X4),k1_funct_1(sK2,X5)),sK1) )
    | ~ spl121_1
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2377,f2193])).

fof(f2193,plain,
    ( v1_relat_1(sK0)
    | ~ spl121_1 ),
    inference(avatar_component_clause,[],[f2191])).

fof(f2191,plain,
    ( spl121_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_1])])).

fof(f2377,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,X5),sK0)
        | r2_hidden(k4_tarski(k1_funct_1(sK2,X4),k1_funct_1(sK2,X5)),sK1)
        | ~ v1_relat_1(sK0) )
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2376,f2198])).

fof(f2198,plain,
    ( v1_relat_1(sK1)
    | ~ spl121_2 ),
    inference(avatar_component_clause,[],[f2196])).

fof(f2196,plain,
    ( spl121_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_2])])).

fof(f2376,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,X5),sK0)
        | r2_hidden(k4_tarski(k1_funct_1(sK2,X4),k1_funct_1(sK2,X5)),sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK0) )
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2375,f2203])).

fof(f2375,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,X5),sK0)
        | r2_hidden(k4_tarski(k1_funct_1(sK2,X4),k1_funct_1(sK2,X5)),sK1)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK0) )
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2361,f2208])).

fof(f2361,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,X5),sK0)
        | r2_hidden(k4_tarski(k1_funct_1(sK2,X4),k1_funct_1(sK2,X5)),sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK0) )
    | ~ spl121_6 ),
    inference(resolution,[],[f2354,f2038])).

fof(f2038,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1655])).

fof(f1655,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK112(X0,X1,X2)),k1_funct_1(X2,sK113(X0,X1,X2))),X1)
                      | ~ r2_hidden(sK113(X0,X1,X2),k3_relat_1(X0))
                      | ~ r2_hidden(sK112(X0,X1,X2),k3_relat_1(X0))
                      | ~ r2_hidden(k4_tarski(sK112(X0,X1,X2),sK113(X0,X1,X2)),X0) )
                    & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,sK112(X0,X1,X2)),k1_funct_1(X2,sK113(X0,X1,X2))),X1)
                        & r2_hidden(sK113(X0,X1,X2),k3_relat_1(X0))
                        & r2_hidden(sK112(X0,X1,X2),k3_relat_1(X0)) )
                      | r2_hidden(k4_tarski(sK112(X0,X1,X2),sK113(X0,X1,X2)),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k3_relat_1(X0) != k1_relat_1(X2) )
                & ( ( ! [X5,X6] :
                        ( ( r2_hidden(k4_tarski(X5,X6),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                          | ~ r2_hidden(X6,k3_relat_1(X0))
                          | ~ r2_hidden(X5,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                            & r2_hidden(X6,k3_relat_1(X0))
                            & r2_hidden(X5,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X5,X6),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k3_relat_1(X0) = k1_relat_1(X2) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK112,sK113])],[f1653,f1654])).

fof(f1654,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
            | ~ r2_hidden(X4,k3_relat_1(X0))
            | ~ r2_hidden(X3,k3_relat_1(X0))
            | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              & r2_hidden(X4,k3_relat_1(X0))
              & r2_hidden(X3,k3_relat_1(X0)) )
            | r2_hidden(k4_tarski(X3,X4),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK112(X0,X1,X2)),k1_funct_1(X2,sK113(X0,X1,X2))),X1)
          | ~ r2_hidden(sK113(X0,X1,X2),k3_relat_1(X0))
          | ~ r2_hidden(sK112(X0,X1,X2),k3_relat_1(X0))
          | ~ r2_hidden(k4_tarski(sK112(X0,X1,X2),sK113(X0,X1,X2)),X0) )
        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,sK112(X0,X1,X2)),k1_funct_1(X2,sK113(X0,X1,X2))),X1)
            & r2_hidden(sK113(X0,X1,X2),k3_relat_1(X0))
            & r2_hidden(sK112(X0,X1,X2),k3_relat_1(X0)) )
          | r2_hidden(k4_tarski(sK112(X0,X1,X2),sK113(X0,X1,X2)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1653,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k3_relat_1(X0) != k1_relat_1(X2) )
                & ( ( ! [X5,X6] :
                        ( ( r2_hidden(k4_tarski(X5,X6),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                          | ~ r2_hidden(X6,k3_relat_1(X0))
                          | ~ r2_hidden(X5,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                            & r2_hidden(X6,k3_relat_1(X0))
                            & r2_hidden(X5,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X5,X6),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k3_relat_1(X0) = k1_relat_1(X2) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1652])).

fof(f1652,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k3_relat_1(X0) != k1_relat_1(X2) )
                & ( ( ! [X3,X4] :
                        ( ( r2_hidden(k4_tarski(X3,X4),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          | ~ r2_hidden(X4,k3_relat_1(X0))
                          | ~ r2_hidden(X3,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                            & r2_hidden(X4,k3_relat_1(X0))
                            & r2_hidden(X3,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k3_relat_1(X0) = k1_relat_1(X2) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1651])).

fof(f1651,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k3_relat_1(X0) != k1_relat_1(X2) )
                & ( ( ! [X3,X4] :
                        ( ( r2_hidden(k4_tarski(X3,X4),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          | ~ r2_hidden(X4,k3_relat_1(X0))
                          | ~ r2_hidden(X3,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                            & r2_hidden(X4,k3_relat_1(X0))
                            & r2_hidden(X3,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k3_relat_1(X0) = k1_relat_1(X2) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1354])).

fof(f1354,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1353])).

fof(f1353,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1137])).

fof(f1137,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).

fof(f2354,plain,
    ( r3_wellord1(sK0,sK1,sK2)
    | ~ spl121_6 ),
    inference(avatar_component_clause,[],[f2352])).

fof(f2352,plain,
    ( spl121_6
  <=> r3_wellord1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_6])])).

fof(f2469,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)
    | spl121_9 ),
    inference(avatar_component_clause,[],[f2467])).

fof(f2467,plain,
    ( spl121_9
  <=> r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_9])])).

fof(f2635,plain,
    ( spl121_15
    | ~ spl121_1
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6
    | ~ spl121_7 ),
    inference(avatar_split_clause,[],[f2458,f2386,f2352,f2206,f2201,f2196,f2191,f2632])).

fof(f2458,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl121_1
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6
    | ~ spl121_7 ),
    inference(forward_demodulation,[],[f2457,f2366])).

fof(f2366,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ spl121_1
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2365,f2193])).

fof(f2365,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2364,f2198])).

fof(f2364,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2363,f2203])).

fof(f2363,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2356,f2208])).

fof(f2356,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl121_6 ),
    inference(resolution,[],[f2354,f2033])).

fof(f2033,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | k3_relat_1(X0) = k1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1655])).

fof(f2457,plain,
    ( r2_hidden(sK4,k3_relat_1(sK0))
    | ~ spl121_1
    | ~ spl121_7 ),
    inference(subsumption_resolution,[],[f2403,f2193])).

fof(f2403,plain,
    ( r2_hidden(sK4,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl121_7 ),
    inference(resolution,[],[f2388,f1949])).

fof(f1949,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1333])).

fof(f1333,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1332])).

fof(f1332,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f833])).

fof(f833,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f2630,plain,
    ( spl121_14
    | ~ spl121_1
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6
    | ~ spl121_7 ),
    inference(avatar_split_clause,[],[f2456,f2386,f2352,f2206,f2201,f2196,f2191,f2627])).

fof(f2456,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl121_1
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6
    | ~ spl121_7 ),
    inference(forward_demodulation,[],[f2455,f2366])).

fof(f2455,plain,
    ( r2_hidden(sK3,k3_relat_1(sK0))
    | ~ spl121_1
    | ~ spl121_7 ),
    inference(subsumption_resolution,[],[f2402,f2193])).

fof(f2402,plain,
    ( r2_hidden(sK3,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl121_7 ),
    inference(resolution,[],[f2388,f1948])).

fof(f1948,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1333])).

fof(f2474,plain,
    ( ~ spl121_9
    | spl121_10 ),
    inference(avatar_split_clause,[],[f1677,f2471,f2467])).

fof(f1677,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) ),
    inference(cnf_transformation,[],[f1392])).

fof(f1392,plain,
    ( ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
      | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) )
    & sK3 != sK4
    & r2_hidden(k4_tarski(sK3,sK4),sK0)
    & r3_wellord1(sK0,sK1,sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f1189,f1391,f1390,f1389,f1388])).

fof(f1388,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3,X4] :
                    ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                      | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                    & X3 != X4
                    & r2_hidden(k4_tarski(X3,X4),X0) )
                & r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X4,X3] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),sK0) )
              & r3_wellord1(sK0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1389,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X4,X3] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                & X3 != X4
                & r2_hidden(k4_tarski(X3,X4),sK0) )
            & r3_wellord1(sK0,X1,X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X4,X3] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK1) )
              & X3 != X4
              & r2_hidden(k4_tarski(X3,X4),sK0) )
          & r3_wellord1(sK0,sK1,X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1390,plain,
    ( ? [X2] :
        ( ? [X4,X3] :
            ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK1) )
            & X3 != X4
            & r2_hidden(k4_tarski(X3,X4),sK0) )
        & r3_wellord1(sK0,sK1,X2)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ? [X4,X3] :
          ( ( k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,X3),k1_funct_1(sK2,X4)),sK1) )
          & X3 != X4
          & r2_hidden(k4_tarski(X3,X4),sK0) )
      & r3_wellord1(sK0,sK1,sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1391,plain,
    ( ? [X4,X3] :
        ( ( k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4)
          | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,X3),k1_funct_1(sK2,X4)),sK1) )
        & X3 != X4
        & r2_hidden(k4_tarski(X3,X4),sK0) )
   => ( ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
        | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) )
      & sK3 != sK4
      & r2_hidden(k4_tarski(sK3,sK4),sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1189,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1188])).

fof(f1188,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1181])).

fof(f1181,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( r3_wellord1(X0,X1,X2)
                 => ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                     => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                          & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                        | X3 = X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1180])).

fof(f1180,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X0)
                   => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                        & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                      | X3 = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_wellord1)).

fof(f2394,plain,
    ( spl121_8
    | ~ spl121_1
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(avatar_split_clause,[],[f2374,f2352,f2206,f2201,f2196,f2191,f2391])).

fof(f2374,plain,
    ( v2_funct_1(sK2)
    | ~ spl121_1
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2373,f2193])).

fof(f2373,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl121_2
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2372,f2198])).

fof(f2372,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl121_3
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2371,f2203])).

fof(f2371,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl121_4
    | ~ spl121_6 ),
    inference(subsumption_resolution,[],[f2358,f2208])).

fof(f2358,plain,
    ( v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl121_6 ),
    inference(resolution,[],[f2354,f2035])).

fof(f2035,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1655])).

fof(f2389,plain,(
    spl121_7 ),
    inference(avatar_split_clause,[],[f1675,f2386])).

fof(f1675,plain,(
    r2_hidden(k4_tarski(sK3,sK4),sK0) ),
    inference(cnf_transformation,[],[f1392])).

fof(f2355,plain,(
    spl121_6 ),
    inference(avatar_split_clause,[],[f1674,f2352])).

fof(f1674,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f1392])).

fof(f2350,plain,(
    ~ spl121_5 ),
    inference(avatar_split_clause,[],[f1676,f2347])).

fof(f1676,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f1392])).

fof(f2209,plain,(
    spl121_4 ),
    inference(avatar_split_clause,[],[f1673,f2206])).

fof(f1673,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1392])).

fof(f2204,plain,(
    spl121_3 ),
    inference(avatar_split_clause,[],[f1672,f2201])).

fof(f1672,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1392])).

fof(f2199,plain,(
    spl121_2 ),
    inference(avatar_split_clause,[],[f1671,f2196])).

fof(f1671,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1392])).

fof(f2194,plain,(
    spl121_1 ),
    inference(avatar_split_clause,[],[f1670,f2191])).

fof(f1670,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1392])).
%------------------------------------------------------------------------------
