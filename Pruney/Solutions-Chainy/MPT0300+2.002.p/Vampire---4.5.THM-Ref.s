%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 460 expanded)
%              Number of leaves         :    9 ( 165 expanded)
%              Depth                    :   18
%              Number of atoms          :  292 (3626 expanded)
%              Number of equality atoms :   70 (1092 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f743,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f345,f398,f612,f742])).

fof(f742,plain,(
    spl9_8 ),
    inference(avatar_contradiction_clause,[],[f741])).

fof(f741,plain,
    ( $false
    | spl9_8 ),
    inference(subsumption_resolution,[],[f740,f16])).

fof(f16,plain,(
    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3)
    & ! [X4,X5] :
        ( ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
          | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) )
        & ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))
          | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
        & ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
              | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
            & ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))
              | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ) )
   => ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3)
      & ! [X5,X4] :
          ( ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
            | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) )
          & ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))
            | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      & ! [X4,X5] :
          ( ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
            | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
          & ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))
            | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      & ! [X4,X5] :
          ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
          <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
       => k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
     => k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_zfmisc_1)).

fof(f740,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | spl9_8 ),
    inference(subsumption_resolution,[],[f736,f626])).

fof(f626,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | spl9_8 ),
    inference(subsumption_resolution,[],[f625,f16])).

fof(f625,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | spl9_8 ),
    inference(resolution,[],[f344,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
              & r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
                & r2_hidden(sK8(X0,X1,X8),X1)
                & r2_hidden(sK7(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f9,f12,f11,f10])).

fof(f10,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
        & r2_hidden(sK8(X0,X1,X8),X1)
        & r2_hidden(sK7(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f344,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl9_8
  <=> r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f736,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | spl9_8 ),
    inference(resolution,[],[f642,f185])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f164,f29])).

fof(f29,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f164,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK7(X3,X1,sK4(X0,X1,X2)),X0)
      | k2_zfmisc_1(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X3,X1)) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | ~ r2_hidden(sK7(X3,X1,sK4(X0,X1,X2)),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X3,X1))
      | ~ r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X3,X1)) ) ),
    inference(resolution,[],[f71,f28])).

fof(f28,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK8(X3,X4,sK4(X0,X1,X2)),X1)
      | k2_zfmisc_1(X0,X1) = X2
      | ~ r2_hidden(sK7(X3,X4,sK4(X0,X1,X2)),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X3,X4)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK4(X3,X4,X5) != X2
      | k2_zfmisc_1(X3,X4) = X5
      | ~ r2_hidden(sK8(X0,X1,X2),X4)
      | ~ r2_hidden(sK7(X0,X1,X2),X3)
      | ~ r2_hidden(sK4(X3,X4,X5),X5)
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f24,f27])).

fof(f27,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) = X2
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f642,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl9_8 ),
    inference(resolution,[],[f626,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK3))
      | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) ) ),
    inference(resolution,[],[f82,f29])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,sK3,X1),sK2)
      | r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,k2_zfmisc_1(X0,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,sK3,X1),sK2)
      | r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,k2_zfmisc_1(X0,sK3))
      | ~ r2_hidden(X1,k2_zfmisc_1(X0,sK3)) ) ),
    inference(resolution,[],[f38,f28])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1,X2),sK3)
      | ~ r2_hidden(sK7(X0,X1,X2),sK2)
      | r2_hidden(X2,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f31,f27])).

fof(f31,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X3,X2),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X2,sK3) ) ),
    inference(resolution,[],[f26,f15])).

fof(f15,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f612,plain,(
    spl9_7 ),
    inference(avatar_contradiction_clause,[],[f611])).

fof(f611,plain,
    ( $false
    | spl9_7 ),
    inference(subsumption_resolution,[],[f610,f16])).

fof(f610,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | spl9_7 ),
    inference(subsumption_resolution,[],[f606,f492])).

fof(f492,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | spl9_7 ),
    inference(subsumption_resolution,[],[f491,f16])).

fof(f491,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | spl9_7 ),
    inference(resolution,[],[f341,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f341,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl9_7
  <=> r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f606,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | spl9_7 ),
    inference(resolution,[],[f560,f185])).

fof(f560,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl9_7 ),
    inference(resolution,[],[f492,f84])).

fof(f398,plain,
    ( ~ spl9_1
    | ~ spl9_8
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f397,f340,f343,f308])).

fof(f308,plain,
    ( spl9_1
  <=> r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f397,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1)
    | ~ r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f364,f16])).

fof(f364,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1)
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f361])).

fof(f361,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1)
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(resolution,[],[f177,f185])).

fof(f177,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(sK6(X2,X3,k2_zfmisc_1(sK2,sK3)),sK1)
      | k2_zfmisc_1(X2,X3) = k2_zfmisc_1(sK2,sK3)
      | ~ r2_hidden(sK5(X2,X3,k2_zfmisc_1(sK2,sK3)),sK0) ) ),
    inference(resolution,[],[f112,f84])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(sK5(X0,X1,k2_zfmisc_1(sK2,sK3)),sK0)
      | ~ r2_hidden(sK6(X0,X1,k2_zfmisc_1(sK2,sK3)),sK1)
      | k2_zfmisc_1(X0,X1) = k2_zfmisc_1(sK2,sK3) ) ),
    inference(factoring,[],[f40])).

fof(f40,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(X3,X4,X5),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(sK5(X3,X4,X5),sK0)
      | ~ r2_hidden(sK6(X3,X4,X5),sK1)
      | k2_zfmisc_1(X3,X4) = X5
      | r2_hidden(sK4(X3,X4,X5),X5) ) ),
    inference(superposition,[],[f30,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f26,f14])).

fof(f14,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f345,plain,
    ( ~ spl9_7
    | ~ spl9_8
    | spl9_1 ),
    inference(avatar_split_clause,[],[f338,f308,f343,f340])).

fof(f338,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0)
    | ~ r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f334,f16])).

fof(f334,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0)
    | ~ r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1)
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | spl9_1 ),
    inference(resolution,[],[f309,f112])).

fof(f309,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:40:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (26532)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (26536)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (26515)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (26528)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (26516)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (26514)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (26534)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (26514)Refutation not found, incomplete strategy% (26514)------------------------------
% 0.21/0.49  % (26514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26514)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (26514)Memory used [KB]: 10618
% 0.21/0.49  % (26514)Time elapsed: 0.073 s
% 0.21/0.49  % (26514)------------------------------
% 0.21/0.49  % (26514)------------------------------
% 0.21/0.50  % (26521)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (26512)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (26511)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (26513)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (26511)Refutation not found, incomplete strategy% (26511)------------------------------
% 0.21/0.50  % (26511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26511)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26511)Memory used [KB]: 6140
% 0.21/0.50  % (26511)Time elapsed: 0.085 s
% 0.21/0.50  % (26511)------------------------------
% 0.21/0.50  % (26511)------------------------------
% 0.21/0.50  % (26537)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (26512)Refutation not found, incomplete strategy% (26512)------------------------------
% 0.21/0.50  % (26512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26533)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (26531)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (26512)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26512)Memory used [KB]: 10618
% 0.21/0.50  % (26512)Time elapsed: 0.085 s
% 0.21/0.50  % (26512)------------------------------
% 0.21/0.50  % (26512)------------------------------
% 0.21/0.50  % (26535)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (26523)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (26533)Refutation not found, incomplete strategy% (26533)------------------------------
% 0.21/0.50  % (26533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26533)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26533)Memory used [KB]: 10618
% 0.21/0.50  % (26533)Time elapsed: 0.089 s
% 0.21/0.50  % (26533)------------------------------
% 0.21/0.50  % (26533)------------------------------
% 0.21/0.50  % (26538)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (26539)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (26539)Refutation not found, incomplete strategy% (26539)------------------------------
% 0.21/0.51  % (26539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26539)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26539)Memory used [KB]: 10618
% 0.21/0.51  % (26539)Time elapsed: 0.097 s
% 0.21/0.51  % (26539)------------------------------
% 0.21/0.51  % (26539)------------------------------
% 0.21/0.51  % (26526)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (26530)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (26530)Refutation not found, incomplete strategy% (26530)------------------------------
% 0.21/0.51  % (26530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26530)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26530)Memory used [KB]: 10618
% 0.21/0.51  % (26530)Time elapsed: 0.099 s
% 0.21/0.51  % (26530)------------------------------
% 0.21/0.51  % (26530)------------------------------
% 0.21/0.51  % (26519)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (26513)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f743,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f345,f398,f612,f742])).
% 0.21/0.52  fof(f742,plain,(
% 0.21/0.52    spl9_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f741])).
% 0.21/0.52  fof(f741,plain,(
% 0.21/0.52    $false | spl9_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f740,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3) & ! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))) & (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) & ! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))) & (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) | ~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))))) => (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3) & ! [X5,X4] : ((r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))) & (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f5,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) & ! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))) & (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) | ~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) & ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))) => k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 0.21/0.52    inference(negated_conjecture,[],[f2])).
% 0.21/0.52  fof(f2,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))) => k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_zfmisc_1)).
% 0.21/0.52  fof(f740,plain,(
% 0.21/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | spl9_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f736,f626])).
% 0.21/0.52  fof(f626,plain,(
% 0.21/0.52    r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) | spl9_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f625,f16])).
% 0.21/0.52  fof(f625,plain,(
% 0.21/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) | spl9_8),
% 0.21/0.52    inference(resolution,[],[f344,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X1) & r2_hidden(sK7(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f9,f12,f11,f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK4(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK4(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X1) & r2_hidden(sK7(X0,X1,X8),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.52    inference(rectify,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.52  fof(f344,plain,(
% 0.21/0.52    ~r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0) | spl9_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f343])).
% 0.21/0.52  fof(f343,plain,(
% 0.21/0.52    spl9_8 <=> r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.52  fof(f736,plain,(
% 0.21/0.52    ~r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | spl9_8),
% 0.21/0.52    inference(resolution,[],[f642,f185])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f180])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(resolution,[],[f164,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK7(X3,X1,sK4(X0,X1,X2)),X0) | k2_zfmisc_1(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X3,X1))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) = X2 | ~r2_hidden(sK7(X3,X1,sK4(X0,X1,X2)),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X3,X1)) | ~r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X3,X1))) )),
% 0.21/0.52    inference(resolution,[],[f71,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X2,X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK8(X3,X4,sK4(X0,X1,X2)),X1) | k2_zfmisc_1(X0,X1) = X2 | ~r2_hidden(sK7(X3,X4,sK4(X0,X1,X2)),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X3,X4))) )),
% 0.21/0.52    inference(equality_resolution,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (sK4(X3,X4,X5) != X2 | k2_zfmisc_1(X3,X4) = X5 | ~r2_hidden(sK8(X0,X1,X2),X4) | ~r2_hidden(sK7(X0,X1,X2),X3) | ~r2_hidden(sK4(X3,X4,X5),X5) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(superposition,[],[f24,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X8,X1] : (k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X2,X0,X8,X1] : (k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X1] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | k2_zfmisc_1(X0,X1) = X2 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f642,plain,(
% 0.21/0.52    r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1)) | spl9_8),
% 0.21/0.52    inference(resolution,[],[f626,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) | r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X0,k2_zfmisc_1(sK2,sK3))) )),
% 0.21/0.52    inference(resolution,[],[f82,f29])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK7(X0,sK3,X1),sK2) | r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,k2_zfmisc_1(X0,sK3))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK7(X0,sK3,X1),sK2) | r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,k2_zfmisc_1(X0,sK3)) | ~r2_hidden(X1,k2_zfmisc_1(X0,sK3))) )),
% 0.21/0.52    inference(resolution,[],[f38,f28])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK8(X0,X1,X2),sK3) | ~r2_hidden(sK7(X0,X1,X2),sK2) | r2_hidden(X2,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(superposition,[],[f31,f27])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r2_hidden(k4_tarski(X3,X2),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X3,sK2) | ~r2_hidden(X2,sK3)) )),
% 0.21/0.52    inference(resolution,[],[f26,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.52    inference(equality_resolution,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f612,plain,(
% 0.21/0.52    spl9_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f611])).
% 0.21/0.52  fof(f611,plain,(
% 0.21/0.52    $false | spl9_7),
% 0.21/0.52    inference(subsumption_resolution,[],[f610,f16])).
% 0.21/0.52  fof(f610,plain,(
% 0.21/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | spl9_7),
% 0.21/0.52    inference(subsumption_resolution,[],[f606,f492])).
% 0.21/0.52  fof(f492,plain,(
% 0.21/0.52    r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) | spl9_7),
% 0.21/0.52    inference(subsumption_resolution,[],[f491,f16])).
% 0.21/0.53  fof(f491,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) | spl9_7),
% 0.21/0.53    inference(resolution,[],[f341,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f341,plain,(
% 0.21/0.53    ~r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1) | spl9_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f340])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    spl9_7 <=> r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.53  fof(f606,plain,(
% 0.21/0.53    ~r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | spl9_7),
% 0.21/0.53    inference(resolution,[],[f560,f185])).
% 0.21/0.53  fof(f560,plain,(
% 0.21/0.53    r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1)) | spl9_7),
% 0.21/0.53    inference(resolution,[],[f492,f84])).
% 0.21/0.53  fof(f398,plain,(
% 0.21/0.53    ~spl9_1 | ~spl9_8 | ~spl9_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f397,f340,f343,f308])).
% 0.21/0.53  fof(f308,plain,(
% 0.21/0.53    spl9_1 <=> r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.53  fof(f397,plain,(
% 0.21/0.53    ~r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1) | ~r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0) | ~r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.53    inference(subsumption_resolution,[],[f364,f16])).
% 0.21/0.53  fof(f364,plain,(
% 0.21/0.53    ~r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | ~r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0) | ~r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f361])).
% 0.21/0.53  fof(f361,plain,(
% 0.21/0.53    ~r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | ~r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0) | ~r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 0.21/0.53    inference(resolution,[],[f177,f185])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK6(X2,X3,k2_zfmisc_1(sK2,sK3)),sK1) | k2_zfmisc_1(X2,X3) = k2_zfmisc_1(sK2,sK3) | ~r2_hidden(sK5(X2,X3,k2_zfmisc_1(sK2,sK3)),sK0)) )),
% 0.21/0.53    inference(resolution,[],[f112,f84])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(sK5(X0,X1,k2_zfmisc_1(sK2,sK3)),sK0) | ~r2_hidden(sK6(X0,X1,k2_zfmisc_1(sK2,sK3)),sK1) | k2_zfmisc_1(X0,X1) = k2_zfmisc_1(sK2,sK3)) )),
% 0.21/0.53    inference(factoring,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (r2_hidden(sK4(X3,X4,X5),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(sK5(X3,X4,X5),sK0) | ~r2_hidden(sK6(X3,X4,X5),sK1) | k2_zfmisc_1(X3,X4) = X5 | r2_hidden(sK4(X3,X4,X5),X5)) )),
% 0.21/0.53    inference(superposition,[],[f30,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f26,f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f345,plain,(
% 0.21/0.53    ~spl9_7 | ~spl9_8 | spl9_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f338,f308,f343,f340])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    ~r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0) | ~r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1) | spl9_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f334,f16])).
% 0.21/0.53  fof(f334,plain,(
% 0.21/0.53    ~r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK0) | ~r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK1) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | spl9_1),
% 0.21/0.53    inference(resolution,[],[f309,f112])).
% 0.21/0.53  fof(f309,plain,(
% 0.21/0.53    ~r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) | spl9_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f308])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (26513)------------------------------
% 0.21/0.53  % (26513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26513)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (26513)Memory used [KB]: 11129
% 0.21/0.53  % (26513)Time elapsed: 0.104 s
% 0.21/0.53  % (26513)------------------------------
% 0.21/0.53  % (26513)------------------------------
% 0.21/0.53  % (26510)Success in time 0.167 s
%------------------------------------------------------------------------------
