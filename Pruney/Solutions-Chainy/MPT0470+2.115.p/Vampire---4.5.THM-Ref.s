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
% DateTime   : Thu Dec  3 12:48:00 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 180 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  253 ( 647 expanded)
%              Number of equality atoms :   56 ( 136 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f560,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f495,f559])).

fof(f559,plain,(
    spl9_2 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | spl9_2 ),
    inference(subsumption_resolution,[],[f536,f33])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f536,plain,
    ( ~ v1_relat_1(sK0)
    | spl9_2 ),
    inference(trivial_inequality_removal,[],[f535])).

fof(f535,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | spl9_2 ),
    inference(superposition,[],[f58,f353])).

fof(f353,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_relat_1(X1,k1_xboole_0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f296,f35])).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f296,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_relat_1(X1,k1_xboole_0)
      | ~ v1_relat_1(X1)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f293,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f293,plain,(
    ! [X30,X31,X32] :
      ( k1_xboole_0 = k5_relat_1(X30,k3_xboole_0(X31,X32))
      | ~ v1_relat_1(X30)
      | ~ r1_xboole_0(X31,X32) ) ),
    inference(subsumption_resolution,[],[f269,f63])).

fof(f63,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f62,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK5(X0)
          & r2_hidden(sK5(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK6(X4),sK7(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f27,f29,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK5(X0)
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK6(X4),sK7(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f62,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f61,f35])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f48,f36])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f15,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f269,plain,(
    ! [X30,X31,X32] :
      ( k1_xboole_0 = k5_relat_1(X30,k3_xboole_0(X31,X32))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X30)
      | ~ r1_xboole_0(X31,X32) ) ),
    inference(resolution,[],[f99,f62])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,k3_xboole_0(X1,X2),X3),sK2(X0,k3_xboole_0(X1,X2),X3)),X3)
      | k5_relat_1(X0,k3_xboole_0(X1,X2)) = X3
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(subsumption_resolution,[],[f97,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f48,f45])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relat_1(X0,k3_xboole_0(X1,X2)) = X3
      | r2_hidden(k4_tarski(sK1(X0,k3_xboole_0(X1,X2),X3),sK2(X0,k3_xboole_0(X1,X2),X3)),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k3_xboole_0(X1,X2))
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f42,f48])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
      | k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f58,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl9_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f495,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f493,f33])).

fof(f493,plain,
    ( ~ v1_relat_1(sK0)
    | spl9_1 ),
    inference(trivial_inequality_removal,[],[f455])).

fof(f455,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | spl9_1 ),
    inference(superposition,[],[f55,f247])).

fof(f247,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f227,f35])).

fof(f227,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X1)
      | ~ v1_relat_1(X1)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f226,f36])).

fof(f226,plain,(
    ! [X30,X31,X32] :
      ( k1_xboole_0 = k5_relat_1(k3_xboole_0(X30,X31),X32)
      | ~ v1_relat_1(X32)
      | ~ r1_xboole_0(X30,X31) ) ),
    inference(subsumption_resolution,[],[f222,f63])).

fof(f222,plain,(
    ! [X30,X31,X32] :
      ( k1_xboole_0 = k5_relat_1(k3_xboole_0(X30,X31),X32)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X32)
      | ~ r1_xboole_0(X30,X31) ) ),
    inference(resolution,[],[f93,f62])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK1(k3_xboole_0(X0,X1),X2,X3),sK2(k3_xboole_0(X0,X1),X2,X3)),X3)
      | k5_relat_1(k3_xboole_0(X0,X1),X2) = X3
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f91,f60])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relat_1(k3_xboole_0(X0,X1),X2) = X3
      | r2_hidden(k4_tarski(sK1(k3_xboole_0(X0,X1),X2,X3),sK2(k3_xboole_0(X0,X1),X2,X3)),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f41,f48])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl9_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f59,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f34,f57,f54])).

fof(f34,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 10:20:27 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.19/0.44  % (31542)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.44  % (31542)Refutation not found, incomplete strategy% (31542)------------------------------
% 0.19/0.44  % (31542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (31542)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.44  
% 0.19/0.44  % (31542)Memory used [KB]: 10618
% 0.19/0.44  % (31542)Time elapsed: 0.052 s
% 0.19/0.44  % (31542)------------------------------
% 0.19/0.44  % (31542)------------------------------
% 0.19/0.44  % (31541)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.45  % (31560)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.45  % (31555)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.46  % (31550)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.46  % (31543)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.46  % (31547)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  % (31544)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.47  % (31549)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.47  % (31557)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.48  % (31554)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.48  % (31541)Refutation not found, incomplete strategy% (31541)------------------------------
% 0.19/0.48  % (31541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (31541)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (31541)Memory used [KB]: 6780
% 0.19/0.48  % (31541)Time elapsed: 0.092 s
% 0.19/0.48  % (31541)------------------------------
% 0.19/0.48  % (31541)------------------------------
% 0.19/0.48  % (31552)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.48  % (31545)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.48  % (31546)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.48  % (31548)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.48  % (31559)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.48  % (31561)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.49  % (31562)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.49  % (31551)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.50  % (31562)Refutation not found, incomplete strategy% (31562)------------------------------
% 0.19/0.50  % (31562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (31562)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (31562)Memory used [KB]: 10618
% 0.19/0.50  % (31562)Time elapsed: 0.115 s
% 0.19/0.50  % (31562)------------------------------
% 0.19/0.50  % (31562)------------------------------
% 0.19/0.50  % (31558)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.50  % (31543)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f560,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f59,f495,f559])).
% 0.19/0.50  fof(f559,plain,(
% 0.19/0.50    spl9_2),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f558])).
% 0.19/0.50  fof(f558,plain,(
% 0.19/0.50    $false | spl9_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f536,f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    v1_relat_1(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f11,plain,(
% 0.19/0.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,negated_conjecture,(
% 0.19/0.50    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.19/0.50    inference(negated_conjecture,[],[f8])).
% 0.19/0.50  fof(f8,conjecture,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.19/0.50  fof(f536,plain,(
% 0.19/0.50    ~v1_relat_1(sK0) | spl9_2),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f535])).
% 0.19/0.50  fof(f535,plain,(
% 0.19/0.50    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | spl9_2),
% 0.19/0.50    inference(superposition,[],[f58,f353])).
% 0.19/0.50  fof(f353,plain,(
% 0.19/0.50    ( ! [X1] : (k1_xboole_0 = k5_relat_1(X1,k1_xboole_0) | ~v1_relat_1(X1)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f296,f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.19/0.50  fof(f296,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_xboole_0 = k5_relat_1(X1,k1_xboole_0) | ~v1_relat_1(X1) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.50    inference(superposition,[],[f293,f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.50  fof(f293,plain,(
% 0.19/0.50    ( ! [X30,X31,X32] : (k1_xboole_0 = k5_relat_1(X30,k3_xboole_0(X31,X32)) | ~v1_relat_1(X30) | ~r1_xboole_0(X31,X32)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f269,f63])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    v1_relat_1(k1_xboole_0)),
% 0.19/0.50    inference(resolution,[],[f62,f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_relat_1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK5(X0) & r2_hidden(sK5(X0),X0))) & (! [X4] : (k4_tarski(sK6(X4),sK7(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f27,f29,f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK5(X0) & r2_hidden(sK5(X0),X0)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK6(X4),sK7(X4)) = X4)),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.19/0.50    inference(rectify,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.19/0.50    inference(nnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f61,f35])).
% 0.19/0.50  fof(f61,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.50    inference(superposition,[],[f48,f36])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f15,f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,plain,(
% 0.19/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.50    inference(rectify,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.19/0.50  fof(f269,plain,(
% 0.19/0.50    ( ! [X30,X31,X32] : (k1_xboole_0 = k5_relat_1(X30,k3_xboole_0(X31,X32)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X30) | ~r1_xboole_0(X31,X32)) )),
% 0.19/0.50    inference(resolution,[],[f99,f62])).
% 0.19/0.50  fof(f99,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK1(X0,k3_xboole_0(X1,X2),X3),sK2(X0,k3_xboole_0(X1,X2),X3)),X3) | k5_relat_1(X0,k3_xboole_0(X1,X2)) = X3 | ~v1_relat_1(X3) | ~v1_relat_1(X0) | ~r1_xboole_0(X1,X2)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f97,f60])).
% 0.19/0.50  fof(f60,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.50    inference(resolution,[],[f48,f45])).
% 0.19/0.50  fof(f97,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k5_relat_1(X0,k3_xboole_0(X1,X2)) = X3 | r2_hidden(k4_tarski(sK1(X0,k3_xboole_0(X1,X2),X3),sK2(X0,k3_xboole_0(X1,X2),X3)),X3) | ~v1_relat_1(X3) | ~v1_relat_1(k3_xboole_0(X1,X2)) | ~v1_relat_1(X0) | ~r1_xboole_0(X1,X2)) )),
% 0.19/0.50    inference(resolution,[],[f42,f48])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) | k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f24,f23,f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2))))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.50    inference(rectify,[],[f20])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.50    inference(nnf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl9_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f57])).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    spl9_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.19/0.50  fof(f495,plain,(
% 0.19/0.50    spl9_1),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f494])).
% 0.19/0.50  fof(f494,plain,(
% 0.19/0.50    $false | spl9_1),
% 0.19/0.50    inference(subsumption_resolution,[],[f493,f33])).
% 0.19/0.50  fof(f493,plain,(
% 0.19/0.50    ~v1_relat_1(sK0) | spl9_1),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f455])).
% 0.19/0.50  fof(f455,plain,(
% 0.19/0.50    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | spl9_1),
% 0.19/0.50    inference(superposition,[],[f55,f247])).
% 0.19/0.50  fof(f247,plain,(
% 0.19/0.50    ( ! [X1] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X1) | ~v1_relat_1(X1)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f227,f35])).
% 0.19/0.50  fof(f227,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X1) | ~v1_relat_1(X1) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.50    inference(superposition,[],[f226,f36])).
% 0.19/0.50  fof(f226,plain,(
% 0.19/0.50    ( ! [X30,X31,X32] : (k1_xboole_0 = k5_relat_1(k3_xboole_0(X30,X31),X32) | ~v1_relat_1(X32) | ~r1_xboole_0(X30,X31)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f222,f63])).
% 0.19/0.50  fof(f222,plain,(
% 0.19/0.50    ( ! [X30,X31,X32] : (k1_xboole_0 = k5_relat_1(k3_xboole_0(X30,X31),X32) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X32) | ~r1_xboole_0(X30,X31)) )),
% 0.19/0.50    inference(resolution,[],[f93,f62])).
% 0.19/0.50  fof(f93,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK1(k3_xboole_0(X0,X1),X2,X3),sK2(k3_xboole_0(X0,X1),X2,X3)),X3) | k5_relat_1(k3_xboole_0(X0,X1),X2) = X3 | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f91,f60])).
% 0.19/0.50  fof(f91,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k5_relat_1(k3_xboole_0(X0,X1),X2) = X3 | r2_hidden(k4_tarski(sK1(k3_xboole_0(X0,X1),X2,X3),sK2(k3_xboole_0(X0,X1),X2,X3)),X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.50    inference(resolution,[],[f41,f48])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) | k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f25])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl9_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f54])).
% 0.19/0.50  fof(f54,plain,(
% 0.19/0.50    spl9_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    ~spl9_1 | ~spl9_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f34,f57,f54])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (31543)------------------------------
% 0.19/0.50  % (31543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (31543)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (31543)Memory used [KB]: 11129
% 0.19/0.50  % (31543)Time elapsed: 0.086 s
% 0.19/0.50  % (31543)------------------------------
% 0.19/0.50  % (31543)------------------------------
% 0.19/0.50  % (31538)Success in time 0.165 s
%------------------------------------------------------------------------------
