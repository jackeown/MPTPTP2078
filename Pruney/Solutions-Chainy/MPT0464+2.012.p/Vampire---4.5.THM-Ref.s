%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:26 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 202 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  328 ( 638 expanded)
%              Number of equality atoms :   81 ( 135 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f130,f164])).

fof(f164,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f162,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X7,X5,X4,X3,X2,X1,X0)
        | ( X5 != X7
          & X4 != X7
          & X3 != X7
          & X2 != X7
          & X1 != X7
          & X0 != X7 ) )
      & ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7
        | ~ sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X7,X5,X4,X3,X2,X1,X0)
        | ( X5 != X7
          & X4 != X7
          & X3 != X7
          & X2 != X7
          & X1 != X7
          & X0 != X7 ) )
      & ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7
        | ~ sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( sP0(X7,X5,X4,X3,X2,X1,X0)
    <=> ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f162,plain,
    ( ~ sP0(sK4,sK4,sK3,sK3,sK3,sK3,sK3)
    | spl6_2 ),
    inference(resolution,[],[f161,f107])).

fof(f107,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X0,k4_enumset1(X6,X5,X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(resolution,[],[f62,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(definition_folding,[],[f23,f25,f24])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6)
      | ~ sP0(X8,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X8,X6) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ~ sP0(X8,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X7,X6) )
          & ( sP0(X7,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X7,X6) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ~ sP0(X8,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ~ sP0(X7,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f161,plain,
    ( ~ r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))
    | spl6_2 ),
    inference(resolution,[],[f160,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f160,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f159,f42])).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))
    & v1_relat_1(sK4)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK2,X1),k5_relat_1(sK2,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK2,X1),k5_relat_1(sK2,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,X2)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,X2)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(f159,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4)
    | ~ v1_relat_1(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f158,f44])).

fof(f44,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f158,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f157,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f157,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK2)
    | spl6_2 ),
    inference(resolution,[],[f123,f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f108,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f47,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f46,f91])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

fof(f123,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK4))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_2
  <=> r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f130,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f128,f42])).

fof(f128,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f127,f43])).

fof(f43,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f127,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f126,f81])).

fof(f126,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f125,f79])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f48,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f125,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl6_1 ),
    inference(resolution,[],[f119,f109])).

fof(f119,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_1
  <=> r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f124,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f115,f121,f117])).

fof(f115,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK4))
    | ~ r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) ),
    inference(resolution,[],[f78,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f77])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f78,plain,(
    ~ r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))) ),
    inference(definition_unfolding,[],[f45,f77,f77])).

fof(f45,plain,(
    ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:25:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (17623)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.56  % (17645)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (17637)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (17628)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.58  % (17627)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (17625)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.70/0.58  % (17630)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.70/0.59  % (17651)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.70/0.59  % (17621)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.70/0.59  % (17626)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.70/0.59  % (17624)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.70/0.60  % (17631)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.70/0.60  % (17646)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.70/0.60  % (17627)Refutation found. Thanks to Tanya!
% 1.70/0.60  % SZS status Theorem for theBenchmark
% 1.70/0.60  % (17646)Refutation not found, incomplete strategy% (17646)------------------------------
% 1.70/0.60  % (17646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.60  % (17633)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.70/0.60  % (17640)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.90/0.61  % (17644)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.90/0.61  % (17649)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.90/0.61  % (17651)Refutation not found, incomplete strategy% (17651)------------------------------
% 1.90/0.61  % (17651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.61  % (17651)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.61  
% 1.90/0.61  % (17651)Memory used [KB]: 1791
% 1.90/0.61  % (17651)Time elapsed: 0.163 s
% 1.90/0.61  % (17651)------------------------------
% 1.90/0.61  % (17651)------------------------------
% 1.90/0.61  % (17650)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.90/0.61  % (17634)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.90/0.61  % (17632)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.90/0.61  % (17629)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.90/0.61  % (17631)Refutation not found, incomplete strategy% (17631)------------------------------
% 1.90/0.61  % (17631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.61  % (17646)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.61  
% 1.90/0.61  % (17646)Memory used [KB]: 10746
% 1.90/0.62  % (17646)Time elapsed: 0.165 s
% 1.90/0.62  % (17646)------------------------------
% 1.90/0.62  % (17646)------------------------------
% 1.90/0.62  % (17636)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.90/0.62  % (17631)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.62  
% 1.90/0.62  % (17631)Memory used [KB]: 10746
% 1.90/0.62  % (17631)Time elapsed: 0.189 s
% 1.90/0.62  % (17631)------------------------------
% 1.90/0.62  % (17631)------------------------------
% 1.90/0.62  % (17647)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.90/0.62  % (17636)Refutation not found, incomplete strategy% (17636)------------------------------
% 1.90/0.62  % (17636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.62  % (17636)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.62  
% 1.90/0.62  % (17636)Memory used [KB]: 1791
% 1.90/0.62  % (17636)Time elapsed: 0.187 s
% 1.90/0.62  % (17636)------------------------------
% 1.90/0.62  % (17636)------------------------------
% 1.90/0.62  % SZS output start Proof for theBenchmark
% 1.90/0.62  fof(f165,plain,(
% 1.90/0.62    $false),
% 1.90/0.62    inference(avatar_sat_refutation,[],[f124,f130,f164])).
% 1.90/0.62  fof(f164,plain,(
% 1.90/0.62    spl6_2),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f163])).
% 1.90/0.62  fof(f163,plain,(
% 1.90/0.62    $false | spl6_2),
% 1.90/0.62    inference(subsumption_resolution,[],[f162,f83])).
% 1.90/0.62  fof(f83,plain,(
% 1.90/0.62    ( ! [X6,X4,X2,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6)) )),
% 1.90/0.62    inference(equality_resolution,[],[f71])).
% 1.90/0.62  fof(f71,plain,(
% 1.90/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6) | X0 != X1) )),
% 1.90/0.62    inference(cnf_transformation,[],[f40])).
% 1.90/0.62  fof(f40,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 1.90/0.62    inference(rectify,[],[f39])).
% 1.90/0.62  fof(f39,plain,(
% 1.90/0.62    ! [X7,X5,X4,X3,X2,X1,X0] : ((sP0(X7,X5,X4,X3,X2,X1,X0) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 1.90/0.62    inference(flattening,[],[f38])).
% 1.90/0.62  fof(f38,plain,(
% 1.90/0.62    ! [X7,X5,X4,X3,X2,X1,X0] : ((sP0(X7,X5,X4,X3,X2,X1,X0) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 1.90/0.62    inference(nnf_transformation,[],[f24])).
% 1.90/0.62  fof(f24,plain,(
% 1.90/0.62    ! [X7,X5,X4,X3,X2,X1,X0] : (sP0(X7,X5,X4,X3,X2,X1,X0) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7))),
% 1.90/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.90/0.62  fof(f162,plain,(
% 1.90/0.62    ~sP0(sK4,sK4,sK3,sK3,sK3,sK3,sK3) | spl6_2),
% 1.90/0.62    inference(resolution,[],[f161,f107])).
% 1.90/0.62  fof(f107,plain,(
% 1.90/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_hidden(X0,k4_enumset1(X6,X5,X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.90/0.62    inference(resolution,[],[f62,f89])).
% 1.90/0.62  fof(f89,plain,(
% 1.90/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 1.90/0.62    inference(equality_resolution,[],[f72])).
% 1.90/0.62  fof(f72,plain,(
% 1.90/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.90/0.62    inference(cnf_transformation,[],[f41])).
% 1.90/0.62  fof(f41,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP1(X0,X1,X2,X3,X4,X5,X6)) & (sP1(X0,X1,X2,X3,X4,X5,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.90/0.62    inference(nnf_transformation,[],[f26])).
% 1.90/0.62  fof(f26,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP1(X0,X1,X2,X3,X4,X5,X6))),
% 1.90/0.62    inference(definition_folding,[],[f23,f25,f24])).
% 1.90/0.62  fof(f25,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : (sP1(X0,X1,X2,X3,X4,X5,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 1.90/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.90/0.62  fof(f23,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 1.90/0.62    inference(ennf_transformation,[],[f8])).
% 1.90/0.62  fof(f8,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).
% 1.90/0.62  fof(f62,plain,(
% 1.90/0.62    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (~sP1(X0,X1,X2,X3,X4,X5,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X6)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f37])).
% 1.90/0.62  fof(f37,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 1.90/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.90/0.62  fof(f36,plain,(
% 1.90/0.62    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6))) => ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 1.90/0.62    introduced(choice_axiom,[])).
% 1.90/0.62  fof(f35,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 1.90/0.62    inference(rectify,[],[f34])).
% 1.90/0.62  fof(f34,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | ~sP0(X7,X5,X4,X3,X2,X1,X0)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 1.90/0.62    inference(nnf_transformation,[],[f25])).
% 1.90/0.62  fof(f161,plain,(
% 1.90/0.62    ~r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) | spl6_2),
% 1.90/0.62    inference(resolution,[],[f160,f51])).
% 1.90/0.62  fof(f51,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f20,plain,(
% 1.90/0.62    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.90/0.62    inference(ennf_transformation,[],[f11])).
% 1.90/0.62  fof(f11,axiom,(
% 1.90/0.62    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.90/0.62  fof(f160,plain,(
% 1.90/0.62    ~r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) | spl6_2),
% 1.90/0.62    inference(subsumption_resolution,[],[f159,f42])).
% 1.90/0.62  fof(f42,plain,(
% 1.90/0.62    v1_relat_1(sK2)),
% 1.90/0.62    inference(cnf_transformation,[],[f30])).
% 1.90/0.62  fof(f30,plain,(
% 1.90/0.62    ((~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))) & v1_relat_1(sK4)) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.90/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f29,f28,f27])).
% 1.90/0.62  fof(f27,plain,(
% 1.90/0.62    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK2,X1),k5_relat_1(sK2,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 1.90/0.62    introduced(choice_axiom,[])).
% 1.90/0.62  fof(f28,plain,(
% 1.90/0.62    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK2,X1),k5_relat_1(sK2,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,X2)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,X2))) & v1_relat_1(X2)) & v1_relat_1(sK3))),
% 1.90/0.62    introduced(choice_axiom,[])).
% 1.90/0.62  fof(f29,plain,(
% 1.90/0.62    ? [X2] : (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,X2)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))) & v1_relat_1(sK4))),
% 1.90/0.62    introduced(choice_axiom,[])).
% 1.90/0.62  fof(f16,plain,(
% 1.90/0.62    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.90/0.62    inference(ennf_transformation,[],[f15])).
% 1.90/0.62  fof(f15,negated_conjecture,(
% 1.90/0.62    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.90/0.62    inference(negated_conjecture,[],[f14])).
% 1.90/0.62  fof(f14,conjecture,(
% 1.90/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).
% 1.90/0.62  fof(f159,plain,(
% 1.90/0.62    ~r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) | ~v1_relat_1(sK2) | spl6_2),
% 1.90/0.62    inference(subsumption_resolution,[],[f158,f44])).
% 1.90/0.62  fof(f44,plain,(
% 1.90/0.62    v1_relat_1(sK4)),
% 1.90/0.62    inference(cnf_transformation,[],[f30])).
% 1.90/0.62  fof(f158,plain,(
% 1.90/0.62    ~r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) | ~v1_relat_1(sK4) | ~v1_relat_1(sK2) | spl6_2),
% 1.90/0.62    inference(subsumption_resolution,[],[f157,f81])).
% 1.90/0.62  fof(f81,plain,(
% 1.90/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.90/0.62    inference(equality_resolution,[],[f53])).
% 1.90/0.62  fof(f53,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.90/0.62    inference(cnf_transformation,[],[f32])).
% 1.90/0.62  fof(f32,plain,(
% 1.90/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.90/0.62    inference(flattening,[],[f31])).
% 1.90/0.62  fof(f31,plain,(
% 1.90/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.90/0.62    inference(nnf_transformation,[],[f1])).
% 1.90/0.62  fof(f1,axiom,(
% 1.90/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.90/0.62  fof(f157,plain,(
% 1.90/0.62    ~r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK4) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK4) | ~v1_relat_1(sK2) | spl6_2),
% 1.90/0.62    inference(resolution,[],[f123,f109])).
% 1.90/0.62  fof(f109,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3) | ~v1_relat_1(X1)) )),
% 1.90/0.62    inference(subsumption_resolution,[],[f108,f91])).
% 1.90/0.62  fof(f91,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 1.90/0.62    inference(resolution,[],[f47,f56])).
% 1.90/0.62  fof(f56,plain,(
% 1.90/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f33])).
% 1.90/0.62  fof(f33,plain,(
% 1.90/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.90/0.62    inference(nnf_transformation,[],[f10])).
% 1.90/0.62  fof(f10,axiom,(
% 1.90/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.90/0.62  fof(f47,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f19])).
% 1.90/0.62  fof(f19,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.90/0.62    inference(ennf_transformation,[],[f12])).
% 1.90/0.62  fof(f12,axiom,(
% 1.90/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.90/0.62  fof(f108,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.90/0.62    inference(subsumption_resolution,[],[f46,f91])).
% 1.90/0.62  fof(f46,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f18,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.90/0.62    inference(flattening,[],[f17])).
% 1.90/0.62  fof(f17,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.90/0.62    inference(ennf_transformation,[],[f13])).
% 1.90/0.62  fof(f13,axiom,(
% 1.90/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).
% 1.90/0.62  fof(f123,plain,(
% 1.90/0.62    ~r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK4)) | spl6_2),
% 1.90/0.62    inference(avatar_component_clause,[],[f121])).
% 1.90/0.62  fof(f121,plain,(
% 1.90/0.62    spl6_2 <=> r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK4))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.90/0.62  fof(f130,plain,(
% 1.90/0.62    spl6_1),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f129])).
% 1.90/0.62  fof(f129,plain,(
% 1.90/0.62    $false | spl6_1),
% 1.90/0.62    inference(subsumption_resolution,[],[f128,f42])).
% 1.90/0.62  fof(f128,plain,(
% 1.90/0.62    ~v1_relat_1(sK2) | spl6_1),
% 1.90/0.62    inference(subsumption_resolution,[],[f127,f43])).
% 1.90/0.62  fof(f43,plain,(
% 1.90/0.62    v1_relat_1(sK3)),
% 1.90/0.62    inference(cnf_transformation,[],[f30])).
% 1.90/0.62  fof(f127,plain,(
% 1.90/0.62    ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | spl6_1),
% 1.90/0.62    inference(subsumption_resolution,[],[f126,f81])).
% 1.90/0.62  fof(f126,plain,(
% 1.90/0.62    ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | spl6_1),
% 1.90/0.62    inference(subsumption_resolution,[],[f125,f79])).
% 1.90/0.62  fof(f79,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f48,f77])).
% 1.90/0.62  fof(f77,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.90/0.62    inference(definition_unfolding,[],[f49,f76])).
% 1.90/0.62  fof(f76,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f50,f75])).
% 1.90/0.62  fof(f75,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f57,f74])).
% 1.90/0.62  fof(f74,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f59,f60])).
% 1.90/0.62  fof(f60,plain,(
% 1.90/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f7])).
% 1.90/0.62  fof(f7,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.90/0.62  fof(f59,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f6])).
% 1.90/0.62  fof(f6,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.90/0.62  fof(f57,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f5])).
% 1.90/0.62  fof(f5,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.90/0.62  fof(f50,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f4])).
% 1.90/0.62  fof(f4,axiom,(
% 1.90/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.90/0.62  fof(f49,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f9])).
% 1.90/0.62  fof(f9,axiom,(
% 1.90/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.90/0.62  fof(f48,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f2])).
% 1.90/0.62  fof(f2,axiom,(
% 1.90/0.62    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.90/0.62  fof(f125,plain,(
% 1.90/0.62    ~r1_tarski(k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),sK3) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | spl6_1),
% 1.90/0.62    inference(resolution,[],[f119,f109])).
% 1.90/0.62  fof(f119,plain,(
% 1.90/0.62    ~r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3)) | spl6_1),
% 1.90/0.62    inference(avatar_component_clause,[],[f117])).
% 1.90/0.62  fof(f117,plain,(
% 1.90/0.62    spl6_1 <=> r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.90/0.62  fof(f124,plain,(
% 1.90/0.62    ~spl6_1 | ~spl6_2),
% 1.90/0.62    inference(avatar_split_clause,[],[f115,f121,f117])).
% 1.90/0.62  fof(f115,plain,(
% 1.90/0.62    ~r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK4)) | ~r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k5_relat_1(sK2,sK3))),
% 1.90/0.62    inference(resolution,[],[f78,f80])).
% 1.90/0.62  fof(f80,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f58,f77])).
% 1.90/0.62  fof(f58,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f22])).
% 1.90/0.62  fof(f22,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.90/0.62    inference(flattening,[],[f21])).
% 1.90/0.62  fof(f21,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.90/0.62    inference(ennf_transformation,[],[f3])).
% 1.90/0.62  fof(f3,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.90/0.62  fof(f78,plain,(
% 1.90/0.62    ~r1_tarski(k5_relat_1(sK2,k1_setfam_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),k1_setfam_1(k4_enumset1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))))),
% 1.90/0.62    inference(definition_unfolding,[],[f45,f77,f77])).
% 1.90/0.62  fof(f45,plain,(
% 1.90/0.62    ~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))),
% 1.90/0.62    inference(cnf_transformation,[],[f30])).
% 1.90/0.62  % SZS output end Proof for theBenchmark
% 1.90/0.62  % (17627)------------------------------
% 1.90/0.62  % (17627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.62  % (17627)Termination reason: Refutation
% 1.90/0.62  
% 1.90/0.62  % (17627)Memory used [KB]: 10746
% 1.90/0.62  % (17627)Time elapsed: 0.173 s
% 1.90/0.62  % (17627)------------------------------
% 1.90/0.62  % (17627)------------------------------
% 1.90/0.62  % (17641)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.90/0.62  % (17622)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.90/0.62  % (17620)Success in time 0.259 s
%------------------------------------------------------------------------------
