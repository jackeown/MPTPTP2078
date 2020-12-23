%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0236+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:18 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 132 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  282 ( 714 expanded)
%              Number of equality atoms :   63 ( 149 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f939,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f670,f705,f937])).

fof(f937,plain,
    ( spl15_4
    | ~ spl15_5 ),
    inference(avatar_contradiction_clause,[],[f936])).

fof(f936,plain,
    ( $false
    | spl15_4
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f893,f935])).

fof(f935,plain,
    ( ! [X12] : r2_hidden(sK1(k1_tarski(sK0),sK0),X12)
    | spl15_4
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f934,f728])).

fof(f728,plain,
    ( ! [X8] : ~ r2_hidden(sK1(k1_tarski(sK0),sK0),k4_xboole_0(sK0,X8))
    | spl15_4 ),
    inference(resolution,[],[f664,f583])).

fof(f583,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f467])).

fof(f467,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f398])).

fof(f398,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f396,f397])).

fof(f397,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f396,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f395])).

fof(f395,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f394])).

fof(f394,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f664,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | spl15_4 ),
    inference(avatar_component_clause,[],[f663])).

fof(f663,plain,
    ( spl15_4
  <=> r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f934,plain,
    ( ! [X12] :
        ( r2_hidden(sK1(k1_tarski(sK0),sK0),k4_xboole_0(sK0,X12))
        | r2_hidden(sK1(k1_tarski(sK0),sK0),X12) )
    | spl15_4
    | ~ spl15_5 ),
    inference(forward_demodulation,[],[f892,f739])).

fof(f739,plain,
    ( sK0 = sK2(k1_tarski(sK0),sK0)
    | ~ spl15_5 ),
    inference(resolution,[],[f669,f594])).

fof(f594,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f490])).

fof(f490,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f414])).

fof(f414,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK8(X0,X1) != X0
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( sK8(X0,X1) = X0
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f412,f413])).

fof(f413,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK8(X0,X1) != X0
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( sK8(X0,X1) = X0
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f412,plain,(
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
    inference(rectify,[],[f411])).

fof(f411,plain,(
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

fof(f669,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f667])).

fof(f667,plain,
    ( spl15_5
  <=> r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f892,plain,
    ( ! [X12] :
        ( r2_hidden(sK1(k1_tarski(sK0),sK0),k4_xboole_0(sK2(k1_tarski(sK0),sK0),X12))
        | r2_hidden(sK1(k1_tarski(sK0),sK0),X12) )
    | spl15_4 ),
    inference(resolution,[],[f711,f581])).

fof(f581,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f469])).

fof(f469,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f398])).

fof(f711,plain,
    ( r2_hidden(sK1(k1_tarski(sK0),sK0),sK2(k1_tarski(sK0),sK0))
    | spl15_4 ),
    inference(subsumption_resolution,[],[f710,f664])).

fof(f710,plain,
    ( r2_hidden(sK1(k1_tarski(sK0),sK0),sK2(k1_tarski(sK0),sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f609])).

fof(f609,plain,(
    ! [X0] :
      ( sK0 != X0
      | r2_hidden(sK1(k1_tarski(sK0),X0),sK2(k1_tarski(sK0),X0))
      | r2_hidden(sK1(k1_tarski(sK0),X0),X0) ) ),
    inference(superposition,[],[f439,f443])).

fof(f443,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f385])).

fof(f385,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f381,f384,f383,f382])).

fof(f382,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f383,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK1(X0,X1),X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f384,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f381,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f380])).

fof(f380,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f439,plain,(
    sK0 != k3_tarski(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f379])).

fof(f379,plain,(
    sK0 != k3_tarski(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f331,f378])).

fof(f378,plain,
    ( ? [X0] : k3_tarski(k1_tarski(X0)) != X0
   => sK0 != k3_tarski(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f331,plain,(
    ? [X0] : k3_tarski(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f324])).

fof(f324,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f323])).

fof(f323,conjecture,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f893,plain,
    ( ! [X13] : ~ r2_hidden(sK1(k1_tarski(sK0),sK0),k4_xboole_0(X13,sK2(k1_tarski(sK0),sK0)))
    | spl15_4 ),
    inference(resolution,[],[f711,f582])).

fof(f582,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f468])).

fof(f468,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f398])).

fof(f705,plain,(
    ~ spl15_4 ),
    inference(avatar_contradiction_clause,[],[f704])).

fof(f704,plain,
    ( $false
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f703,f665])).

fof(f665,plain,
    ( r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f663])).

fof(f703,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f702,f593])).

fof(f593,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f592])).

fof(f592,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f491])).

fof(f491,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f414])).

fof(f702,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f671,f439])).

fof(f671,plain,
    ( sK0 = k3_tarski(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | ~ spl15_4 ),
    inference(resolution,[],[f665,f445])).

fof(f445,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK1(X0,X1),X3)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f385])).

fof(f670,plain,
    ( spl15_4
    | spl15_5 ),
    inference(avatar_split_clause,[],[f661,f667,f663])).

fof(f661,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f610])).

fof(f610,plain,(
    ! [X1] :
      ( sK0 != X1
      | r2_hidden(sK2(k1_tarski(sK0),X1),k1_tarski(sK0))
      | r2_hidden(sK1(k1_tarski(sK0),X1),X1) ) ),
    inference(superposition,[],[f439,f444])).

fof(f444,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f385])).
%------------------------------------------------------------------------------
