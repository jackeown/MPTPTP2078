%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 185 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  342 ( 684 expanded)
%              Number of equality atoms :   62 ( 100 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f64,f68,f88,f143,f181,f187,f191,f202,f274,f294,f296])).

fof(f296,plain,
    ( ~ spl6_14
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f213,f200,f179])).

fof(f179,plain,
    ( spl6_14
  <=> r1_xboole_0(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f200,plain,
    ( spl6_18
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f213,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | ~ spl6_18 ),
    inference(resolution,[],[f201,f28])).

fof(f28,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f201,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f200])).

fof(f294,plain,
    ( ~ spl6_15
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl6_15
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f186,f272])).

fof(f272,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl6_26
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f186,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_15
  <=> r2_hidden(sK4(sK5(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f274,plain,
    ( spl6_26
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f267,f189,f185,f271])).

fof(f189,plain,
    ( spl6_16
  <=> r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK5(sK0),sK0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_16 ),
    inference(resolution,[],[f190,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f25])).

fof(f25,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f190,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f189])).

fof(f202,plain,
    ( spl6_18
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f194,f138,f200])).

fof(f138,plain,
    ( spl6_9
  <=> r2_hidden(sK4(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f194,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f139,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK5(X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f139,plain,
    ( r2_hidden(sK4(sK0,sK0),sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f191,plain,
    ( spl6_16
    | spl6_14 ),
    inference(avatar_split_clause,[],[f183,f179,f189])).

fof(f183,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))
    | spl6_14 ),
    inference(resolution,[],[f180,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
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
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f180,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f179])).

fof(f187,plain,
    ( spl6_15
    | spl6_14 ),
    inference(avatar_split_clause,[],[f182,f179,f185])).

fof(f182,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK0)
    | spl6_14 ),
    inference(resolution,[],[f180,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f181,plain,
    ( ~ spl6_14
    | spl6_1
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f176,f141,f52,f179])).

fof(f52,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f141,plain,
    ( spl6_10
  <=> ! [X0] :
        ( r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f176,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_xboole_0(sK5(sK0),sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f145,f28])).

fof(f145,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(X2),X2)
        | k1_xboole_0 = X2 )
    | ~ spl6_10 ),
    inference(resolution,[],[f142,f44])).

fof(f142,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl6_9
    | spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f136,f86,f141,f138])).

fof(f86,plain,
    ( spl6_7
  <=> ! [X3,X4] :
        ( k1_xboole_0 = X4
        | r2_hidden(sK1(k1_xboole_0,X3,X4),X4)
        | r2_hidden(sK2(k1_xboole_0,X3,X4),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f136,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | k1_xboole_0 = X0
        | r2_hidden(sK4(sK0,sK0),sK0) )
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | k1_xboole_0 = X0
        | r2_hidden(sK4(sK0,sK0),sK0)
        | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_7 ),
    inference(resolution,[],[f122,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2(k1_xboole_0,sK0,X0),sK0),sK0)
        | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_7 ),
    inference(resolution,[],[f96,f42])).

fof(f96,plain,
    ( ! [X18] :
        ( ~ r1_xboole_0(sK2(k1_xboole_0,sK0,X18),sK0)
        | k1_xboole_0 = X18
        | r2_hidden(sK1(k1_xboole_0,sK0,X18),X18) )
    | ~ spl6_7 ),
    inference(resolution,[],[f87,f28])).

fof(f87,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(k1_xboole_0,X3,X4),X3)
        | r2_hidden(sK1(k1_xboole_0,X3,X4),X4)
        | k1_xboole_0 = X4 )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK2(k1_xboole_0,sK0,X0),sK0),X1)
        | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | k1_xboole_0 = X0
        | r2_hidden(sK4(X1,sK0),sK0) )
    | ~ spl6_7 ),
    inference(resolution,[],[f101,f42])).

fof(f101,plain,
    ( ! [X2,X1] :
        ( ~ r1_xboole_0(X2,sK0)
        | k1_xboole_0 = X1
        | r2_hidden(sK1(k1_xboole_0,sK0,X1),X1)
        | ~ r2_hidden(sK4(sK2(k1_xboole_0,sK0,X1),sK0),X2) )
    | ~ spl6_7 ),
    inference(resolution,[],[f98,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,
    ( ~ spl6_4
    | spl6_7
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f84,f62,f86,f66])).

fof(f66,plain,
    ( spl6_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f62,plain,
    ( spl6_3
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f84,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 = X4
        | r2_hidden(sK2(k1_xboole_0,X3,X4),X3)
        | r2_hidden(sK1(k1_xboole_0,X3,X4),X4)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f82,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f82,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(k1_xboole_0,X3,X4),X3)
        | r2_hidden(sK1(k1_xboole_0,X3,X4),X4)
        | k9_relat_1(k1_xboole_0,X3) = X4
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f38,f63])).

fof(f63,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( sK1(X0,X1,X2) = k1_funct_1(X0,sK2(X0,X1,X2))
                  & r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
                    & r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK1(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK1(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK1(X0,X1,X2) = k1_funct_1(X0,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f68,plain,
    ( spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f60,f56,f66])).

fof(f56,plain,
    ( spl6_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f60,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(superposition,[],[f31,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f64,plain,
    ( spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f59,f56,f62])).

fof(f59,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(superposition,[],[f32,f57])).

fof(f32,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f54,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:36:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (23174)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (23184)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (23176)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (23176)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (23183)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (23183)Refutation not found, incomplete strategy% (23183)------------------------------
% 0.21/0.51  % (23183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23183)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23183)Memory used [KB]: 1663
% 0.21/0.51  % (23183)Time elapsed: 0.084 s
% 0.21/0.51  % (23183)------------------------------
% 0.21/0.51  % (23183)------------------------------
% 0.21/0.51  % (23172)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f54,f58,f64,f68,f88,f143,f181,f187,f191,f202,f274,f294,f296])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    ~spl6_14 | ~spl6_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f213,f200,f179])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl6_14 <=> r1_xboole_0(sK5(sK0),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    spl6_18 <=> r2_hidden(sK5(sK0),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    ~r1_xboole_0(sK5(sK0),sK0) | ~spl6_18),
% 0.21/0.51    inference(resolution,[],[f201,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    r2_hidden(sK5(sK0),sK0) | ~spl6_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f200])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    ~spl6_15 | ~spl6_26),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f288])).
% 0.21/0.51  fof(f288,plain,(
% 0.21/0.51    $false | (~spl6_15 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f186,f272])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl6_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f271])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    spl6_26 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    r2_hidden(sK4(sK5(sK0),sK0),sK0) | ~spl6_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f185])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    spl6_15 <=> r2_hidden(sK4(sK5(sK0),sK0),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    spl6_26 | ~spl6_15 | ~spl6_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f267,f189,f185,f271])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    spl6_16 <=> r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK4(sK5(sK0),sK0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl6_16),
% 0.21/0.51    inference(resolution,[],[f190,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) | ~spl6_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f189])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    spl6_18 | ~spl6_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f194,f138,f200])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    spl6_9 <=> r2_hidden(sK4(sK0,sK0),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    r2_hidden(sK5(sK0),sK0) | ~spl6_9),
% 0.21/0.51    inference(resolution,[],[f139,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK5(X1),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,sK0),sK0) | ~spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f138])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    spl6_16 | spl6_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f183,f179,f189])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) | spl6_14),
% 0.21/0.51    inference(resolution,[],[f180,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~r1_xboole_0(sK5(sK0),sK0) | spl6_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f179])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    spl6_15 | spl6_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f182,f179,f185])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    r2_hidden(sK4(sK5(sK0),sK0),sK0) | spl6_14),
% 0.21/0.51    inference(resolution,[],[f180,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    ~spl6_14 | spl6_1 | ~spl6_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f176,f141,f52,f179])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    spl6_1 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl6_10 <=> ! [X0] : (r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~r1_xboole_0(sK5(sK0),sK0) | ~spl6_10),
% 0.21/0.51    inference(resolution,[],[f145,f28])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ( ! [X2] : (r2_hidden(sK5(X2),X2) | k1_xboole_0 = X2) ) | ~spl6_10),
% 0.21/0.51    inference(resolution,[],[f142,f44])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | k1_xboole_0 = X0) ) | ~spl6_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f141])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl6_9 | spl6_10 | ~spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f136,f86,f141,f138])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl6_7 <=> ! [X3,X4] : (k1_xboole_0 = X4 | r2_hidden(sK1(k1_xboole_0,X3,X4),X4) | r2_hidden(sK2(k1_xboole_0,X3,X4),X3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,sK0),sK0)) ) | ~spl6_7),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f133])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,sK0),sK0) | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | k1_xboole_0 = X0) ) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f122,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK4(sK2(k1_xboole_0,sK0,X0),sK0),sK0) | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | k1_xboole_0 = X0) ) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f96,f42])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X18] : (~r1_xboole_0(sK2(k1_xboole_0,sK0,X18),sK0) | k1_xboole_0 = X18 | r2_hidden(sK1(k1_xboole_0,sK0,X18),X18)) ) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f87,f28])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X4,X3] : (r2_hidden(sK2(k1_xboole_0,X3,X4),X3) | r2_hidden(sK1(k1_xboole_0,X3,X4),X4) | k1_xboole_0 = X4) ) | ~spl6_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(sK2(k1_xboole_0,sK0,X0),sK0),X1) | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | k1_xboole_0 = X0 | r2_hidden(sK4(X1,sK0),sK0)) ) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f101,f42])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~r1_xboole_0(X2,sK0) | k1_xboole_0 = X1 | r2_hidden(sK1(k1_xboole_0,sK0,X1),X1) | ~r2_hidden(sK4(sK2(k1_xboole_0,sK0,X1),sK0),X2)) ) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f98,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~spl6_4 | spl6_7 | ~spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f84,f62,f86,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl6_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl6_3 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k1_xboole_0 = X4 | r2_hidden(sK2(k1_xboole_0,X3,X4),X3) | r2_hidden(sK1(k1_xboole_0,X3,X4),X4) | ~v1_relat_1(k1_xboole_0)) ) | ~spl6_3),
% 0.21/0.51    inference(forward_demodulation,[],[f82,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X4,X3] : (r2_hidden(sK2(k1_xboole_0,X3,X4),X3) | r2_hidden(sK1(k1_xboole_0,X3,X4),X4) | k9_relat_1(k1_xboole_0,X3) = X4 | ~v1_relat_1(k1_xboole_0)) ) | ~spl6_3),
% 0.21/0.51    inference(resolution,[],[f38,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    v1_funct_1(k1_xboole_0) | ~spl6_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f62])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | k9_relat_1(X0,X1) = X2 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((sK1(X0,X1,X2) = k1_funct_1(X0,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f21,f20,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK1(X0,X1,X2) = k1_funct_1(X0,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(rectify,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl6_4 | ~spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f60,f56,f66])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl6_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    v1_relat_1(k1_xboole_0) | ~spl6_2),
% 0.21/0.51    inference(superposition,[],[f31,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl6_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f56])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl6_3 | ~spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f59,f56,f62])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    v1_funct_1(k1_xboole_0) | ~spl6_2),
% 0.21/0.51    inference(superposition,[],[f32,f57])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f56])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ~spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f27,f52])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (23176)------------------------------
% 0.21/0.51  % (23176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23176)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (23176)Memory used [KB]: 10746
% 0.21/0.51  % (23176)Time elapsed: 0.087 s
% 0.21/0.51  % (23176)------------------------------
% 0.21/0.51  % (23176)------------------------------
% 0.21/0.51  % (23173)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (23169)Success in time 0.152 s
%------------------------------------------------------------------------------
