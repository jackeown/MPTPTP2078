%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0300+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 170 expanded)
%              Number of leaves         :   14 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 (1097 expanded)
%              Number of equality atoms :   61 ( 311 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f135,f140,f182,f209,f233,f234,f281,f282,f284])).

fof(f284,plain,
    ( ~ spl9_2
    | spl9_28 ),
    inference(avatar_split_clause,[],[f283,f247,f95])).

fof(f95,plain,
    ( spl9_2
  <=> r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f247,plain,
    ( spl9_28
  <=> r2_hidden(sK7(sK0,sK1,sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f283,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl9_28 ),
    inference(resolution,[],[f248,f29])).

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

fof(f248,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3))),sK0)
    | spl9_28 ),
    inference(avatar_component_clause,[],[f247])).

fof(f282,plain,
    ( spl9_1
    | ~ spl9_13
    | ~ spl9_28
    | ~ spl9_27
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f275,f95,f244,f247,f133,f31])).

fof(f31,plain,
    ( spl9_1
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f133,plain,
    ( spl9_13
  <=> r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f244,plain,
    ( spl9_27
  <=> r2_hidden(sK8(sK0,sK1,sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f275,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3))),sK1)
    | ~ r2_hidden(sK7(sK0,sK1,sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3))),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f208,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(X3,X4))
      | ~ r2_hidden(sK8(X3,X4,sK4(X0,X1,X2)),X1)
      | ~ r2_hidden(sK7(X3,X4,sK4(X0,X1,X2)),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
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

fof(f208,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f281,plain,
    ( ~ spl9_2
    | spl9_27 ),
    inference(avatar_split_clause,[],[f280,f244,f95])).

fof(f280,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl9_27 ),
    inference(resolution,[],[f245,f28])).

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

fof(f245,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3))),sK1)
    | spl9_27 ),
    inference(avatar_component_clause,[],[f244])).

fof(f234,plain,
    ( ~ spl9_2
    | spl9_13
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f173,f98,f133,f95])).

fof(f98,plain,
    ( spl9_3
  <=> sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)) = k4_tarski(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f173,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_3 ),
    inference(superposition,[],[f14,f99])).

fof(f99,plain,
    ( sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)) = k4_tarski(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f14,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) ) ),
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

fof(f233,plain,
    ( ~ spl9_12
    | ~ spl9_13 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f178,f131])).

fof(f131,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(X0,X1))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl9_12
  <=> ! [X1,X0] : ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f178,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f209,plain,
    ( spl9_13
    | spl9_1
    | spl9_2
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f204,f180,f95,f31,f133])).

fof(f180,plain,
    ( spl9_16
  <=> ! [X0] :
        ( r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(X0,sK1))
        | ~ r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f204,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | ~ spl9_16 ),
    inference(resolution,[],[f181,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),X0)
        | r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(X0,sK1)) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl9_13
    | spl9_1
    | spl9_16
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f174,f98,f180,f31,f133])).

fof(f174,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(X0,sK1))
        | ~ r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),X0)
        | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
        | r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f171,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f171,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)),X4)
        | r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(X3,X4))
        | ~ r2_hidden(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),X3) )
    | ~ spl9_3 ),
    inference(superposition,[],[f26,f99])).

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

fof(f140,plain,
    ( spl9_1
    | spl9_3
    | spl9_13 ),
    inference(avatar_split_clause,[],[f138,f133,f98,f31])).

fof(f138,plain,
    ( sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)) = k4_tarski(sK5(sK0,sK1,k2_zfmisc_1(sK2,sK3)),sK6(sK0,sK1,k2_zfmisc_1(sK2,sK3)))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | spl9_13 ),
    inference(resolution,[],[f134,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f134,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | spl9_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl9_12
    | ~ spl9_13
    | spl9_2 ),
    inference(avatar_split_clause,[],[f127,f95,f133,f130])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
        | ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(X0,X1)) )
    | spl9_2 ),
    inference(resolution,[],[f96,f35])).

fof(f35,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(X7,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X7,k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X7,k2_zfmisc_1(X5,X6)) ) ),
    inference(superposition,[],[f15,f27])).

fof(f15,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f96,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f33,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
