%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:51 EST 2020

% Result     : Theorem 4.39s
% Output     : Refutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 177 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  322 ( 761 expanded)
%              Number of equality atoms :  106 ( 305 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4845,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f686,f690,f1226,f2297,f3315,f4759,f4844])).

fof(f4844,plain,
    ( spl29_1
    | spl29_12 ),
    inference(avatar_contradiction_clause,[],[f4843])).

fof(f4843,plain,
    ( $false
    | spl29_1
    | spl29_12 ),
    inference(subsumption_resolution,[],[f4762,f2296])).

fof(f2296,plain,
    ( ~ r2_hidden(sK6(k1_tarski(sK0),sK0),sK0)
    | spl29_12 ),
    inference(avatar_component_clause,[],[f2294])).

fof(f2294,plain,
    ( spl29_12
  <=> r2_hidden(sK6(k1_tarski(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_12])])).

fof(f4762,plain,
    ( r2_hidden(sK6(k1_tarski(sK0),sK0),sK0)
    | spl29_1
    | spl29_12 ),
    inference(unit_resulting_resolution,[],[f677,f619,f297,f2296,f359])).

fof(f359,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f221])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK6(X0,X1),sK7(X0,X1))
                  & r2_hidden(sK7(X0,X1),X0) )
                | ~ r2_hidden(sK6(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK6(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK6(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK8(X0,X5))
                    & r2_hidden(sK8(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f217,f220,f219,f218])).

fof(f218,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK6(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK6(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f219,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK6(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f220,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK8(X0,X5))
        & r2_hidden(sK8(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f127])).

fof(f127,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f297,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f204])).

fof(f204,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f144,f203])).

fof(f203,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f144,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f139])).

fof(f139,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f138])).

fof(f138,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f619,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f618])).

fof(f618,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f418])).

fof(f418,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f257])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK22(X0,X1) != X0
            | ~ r2_hidden(sK22(X0,X1),X1) )
          & ( sK22(X0,X1) = X0
            | r2_hidden(sK22(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f255,f256])).

fof(f256,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK22(X0,X1) != X0
          | ~ r2_hidden(sK22(X0,X1),X1) )
        & ( sK22(X0,X1) = X0
          | r2_hidden(sK22(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f255,plain,(
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
    inference(rectify,[],[f254])).

fof(f254,plain,(
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
    inference(nnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f677,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl29_1 ),
    inference(avatar_component_clause,[],[f676])).

fof(f676,plain,
    ( spl29_1
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_1])])).

fof(f4759,plain,
    ( ~ spl29_12
    | ~ spl29_11
    | spl29_14 ),
    inference(avatar_split_clause,[],[f4714,f3312,f2290,f2294])).

fof(f2290,plain,
    ( spl29_11
  <=> r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_11])])).

fof(f3312,plain,
    ( spl29_14
  <=> r2_hidden(sK6(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_14])])).

fof(f4714,plain,
    ( ~ r2_hidden(sK6(k1_tarski(sK0),sK0),sK0)
    | ~ spl29_11
    | spl29_14 ),
    inference(backward_demodulation,[],[f3314,f4617])).

fof(f4617,plain,
    ( sK0 = sK7(k1_tarski(sK0),sK0)
    | ~ spl29_11 ),
    inference(unit_resulting_resolution,[],[f2292,f620])).

fof(f620,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f417])).

fof(f417,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f257])).

fof(f2292,plain,
    ( r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ spl29_11 ),
    inference(avatar_component_clause,[],[f2290])).

fof(f3314,plain,
    ( ~ r2_hidden(sK6(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0))
    | spl29_14 ),
    inference(avatar_component_clause,[],[f3312])).

fof(f3315,plain,
    ( ~ spl29_14
    | ~ spl29_12
    | ~ spl29_4 ),
    inference(avatar_split_clause,[],[f2298,f688,f2294,f3312])).

fof(f688,plain,
    ( spl29_4
  <=> ! [X3] :
        ( sK0 != X3
        | ~ r2_hidden(sK6(k1_tarski(sK0),X3),X3)
        | ~ r2_hidden(sK6(k1_tarski(sK0),X3),sK7(k1_tarski(sK0),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_4])])).

fof(f2298,plain,
    ( ~ r2_hidden(sK6(k1_tarski(sK0),sK0),sK0)
    | ~ r2_hidden(sK6(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0))
    | ~ spl29_4 ),
    inference(equality_resolution,[],[f689])).

fof(f689,plain,
    ( ! [X3] :
        ( sK0 != X3
        | ~ r2_hidden(sK6(k1_tarski(sK0),X3),X3)
        | ~ r2_hidden(sK6(k1_tarski(sK0),X3),sK7(k1_tarski(sK0),X3)) )
    | ~ spl29_4 ),
    inference(avatar_component_clause,[],[f688])).

fof(f2297,plain,
    ( spl29_11
    | ~ spl29_12
    | ~ spl29_3 ),
    inference(avatar_split_clause,[],[f2288,f684,f2294,f2290])).

fof(f684,plain,
    ( spl29_3
  <=> ! [X2] :
        ( sK0 != X2
        | ~ r2_hidden(sK6(k1_tarski(sK0),X2),X2)
        | r2_hidden(sK7(k1_tarski(sK0),X2),k1_tarski(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_3])])).

fof(f2288,plain,
    ( ~ r2_hidden(sK6(k1_tarski(sK0),sK0),sK0)
    | r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ spl29_3 ),
    inference(equality_resolution,[],[f685])).

fof(f685,plain,
    ( ! [X2] :
        ( sK0 != X2
        | ~ r2_hidden(sK6(k1_tarski(sK0),X2),X2)
        | r2_hidden(sK7(k1_tarski(sK0),X2),k1_tarski(sK0)) )
    | ~ spl29_3 ),
    inference(avatar_component_clause,[],[f684])).

fof(f1226,plain,(
    ~ spl29_1 ),
    inference(avatar_contradiction_clause,[],[f1225])).

fof(f1225,plain,
    ( $false
    | ~ spl29_1 ),
    inference(subsumption_resolution,[],[f1036,f602])).

fof(f602,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f314])).

fof(f314,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f1036,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl29_1 ),
    inference(unit_resulting_resolution,[],[f972,f972,f368])).

fof(f368,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f151,f224])).

fof(f224,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f972,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl29_1 ),
    inference(forward_demodulation,[],[f971,f304])).

fof(f304,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f971,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_xboole_0,k1_tarski(k1_xboole_0)))
    | ~ spl29_1 ),
    inference(forward_demodulation,[],[f958,f678])).

fof(f678,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl29_1 ),
    inference(avatar_component_clause,[],[f676])).

fof(f958,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_tarski(sK0),k1_tarski(k1_xboole_0)))
    | ~ spl29_1 ),
    inference(unit_resulting_resolution,[],[f619,f895,f506])).

fof(f506,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f292])).

fof(f292,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f291])).

fof(f291,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f104])).

fof(f104,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f895,plain,
    ( k1_xboole_0 != sK0
    | ~ spl29_1 ),
    inference(forward_demodulation,[],[f822,f298])).

fof(f298,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f130])).

fof(f130,axiom,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_setfam_1)).

fof(f822,plain,
    ( k1_setfam_1(k1_xboole_0) != sK0
    | ~ spl29_1 ),
    inference(backward_demodulation,[],[f297,f678])).

fof(f690,plain,
    ( spl29_1
    | spl29_4 ),
    inference(avatar_split_clause,[],[f673,f688,f676])).

fof(f673,plain,(
    ! [X3] :
      ( sK0 != X3
      | ~ r2_hidden(sK6(k1_tarski(sK0),X3),sK7(k1_tarski(sK0),X3))
      | ~ r2_hidden(sK6(k1_tarski(sK0),X3),X3)
      | k1_xboole_0 = k1_tarski(sK0) ) ),
    inference(superposition,[],[f297,f361])).

fof(f361,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK6(X0,X1),sK7(X0,X1))
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f221])).

fof(f686,plain,
    ( spl29_1
    | spl29_3 ),
    inference(avatar_split_clause,[],[f672,f684,f676])).

fof(f672,plain,(
    ! [X2] :
      ( sK0 != X2
      | r2_hidden(sK7(k1_tarski(sK0),X2),k1_tarski(sK0))
      | ~ r2_hidden(sK6(k1_tarski(sK0),X2),X2)
      | k1_xboole_0 = k1_tarski(sK0) ) ),
    inference(superposition,[],[f297,f360])).

fof(f360,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK7(X0,X1),X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:05:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (2028)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (2043)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (2035)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (2044)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (2025)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (2027)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (2043)Refutation not found, incomplete strategy% (2043)------------------------------
% 0.20/0.52  % (2043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2034)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (2043)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2043)Memory used [KB]: 11129
% 0.20/0.52  % (2043)Time elapsed: 0.075 s
% 0.20/0.52  % (2043)------------------------------
% 0.20/0.52  % (2043)------------------------------
% 0.20/0.52  % (2036)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (2023)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (2021)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (2049)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (2048)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (2022)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (2024)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (2023)Refutation not found, incomplete strategy% (2023)------------------------------
% 0.20/0.53  % (2023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2023)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2023)Memory used [KB]: 11129
% 0.20/0.54  % (2023)Time elapsed: 0.133 s
% 0.20/0.54  % (2023)------------------------------
% 0.20/0.54  % (2023)------------------------------
% 0.20/0.54  % (2026)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (2047)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (2041)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (2031)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (2038)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (2039)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (2040)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (2041)Refutation not found, incomplete strategy% (2041)------------------------------
% 0.20/0.55  % (2041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2041)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2041)Memory used [KB]: 11001
% 0.20/0.55  % (2041)Time elapsed: 0.148 s
% 0.20/0.55  % (2041)------------------------------
% 0.20/0.55  % (2041)------------------------------
% 0.20/0.55  % (2033)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (2030)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (2032)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (2050)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.54/0.56  % (2046)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.54/0.56  % (2037)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.54/0.56  % (2042)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.54/0.56  % (2045)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.54/0.56  % (2029)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.54/0.57  % (2029)Refutation not found, incomplete strategy% (2029)------------------------------
% 1.54/0.57  % (2029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (2029)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (2029)Memory used [KB]: 11001
% 1.54/0.57  % (2029)Time elapsed: 0.163 s
% 1.54/0.57  % (2029)------------------------------
% 1.54/0.57  % (2029)------------------------------
% 1.65/0.59  % (2042)Refutation not found, incomplete strategy% (2042)------------------------------
% 1.65/0.59  % (2042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (2042)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (2042)Memory used [KB]: 2046
% 1.65/0.59  % (2042)Time elapsed: 0.186 s
% 1.65/0.59  % (2042)------------------------------
% 1.65/0.59  % (2042)------------------------------
% 2.08/0.65  % (2052)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.24/0.69  % (2053)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.24/0.70  % (2056)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.24/0.71  % (2055)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.24/0.72  % (2054)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.07/0.81  % (2026)Time limit reached!
% 3.07/0.81  % (2026)------------------------------
% 3.07/0.81  % (2026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.81  % (2026)Termination reason: Time limit
% 3.07/0.81  
% 3.07/0.81  % (2026)Memory used [KB]: 8955
% 3.07/0.81  % (2026)Time elapsed: 0.405 s
% 3.07/0.81  % (2026)------------------------------
% 3.07/0.81  % (2026)------------------------------
% 3.83/0.90  % (2031)Time limit reached!
% 3.83/0.90  % (2031)------------------------------
% 3.83/0.90  % (2031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.91  % (2021)Time limit reached!
% 3.83/0.91  % (2021)------------------------------
% 3.83/0.91  % (2021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.91  % (2021)Termination reason: Time limit
% 3.83/0.91  
% 3.83/0.91  % (2021)Memory used [KB]: 4349
% 3.83/0.91  % (2021)Time elapsed: 0.501 s
% 3.83/0.91  % (2021)------------------------------
% 3.83/0.91  % (2021)------------------------------
% 3.83/0.91  % (2031)Termination reason: Time limit
% 3.83/0.91  % (2031)Termination phase: Saturation
% 3.83/0.91  
% 3.83/0.91  % (2031)Memory used [KB]: 14200
% 3.83/0.91  % (2031)Time elapsed: 0.500 s
% 3.83/0.91  % (2031)------------------------------
% 3.83/0.91  % (2031)------------------------------
% 3.83/0.91  % (2033)Time limit reached!
% 3.83/0.91  % (2033)------------------------------
% 3.83/0.91  % (2033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.92  % (2038)Time limit reached!
% 3.83/0.92  % (2038)------------------------------
% 3.83/0.92  % (2038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.92  % (2038)Termination reason: Time limit
% 3.83/0.92  
% 3.83/0.92  % (2038)Memory used [KB]: 14456
% 3.83/0.92  % (2038)Time elapsed: 0.519 s
% 3.83/0.92  % (2038)------------------------------
% 3.83/0.92  % (2038)------------------------------
% 3.83/0.92  % (2033)Termination reason: Time limit
% 3.83/0.92  % (2033)Termination phase: Saturation
% 3.83/0.92  
% 3.83/0.92  % (2033)Memory used [KB]: 9083
% 3.83/0.92  % (2033)Time elapsed: 0.500 s
% 3.83/0.92  % (2033)------------------------------
% 3.83/0.92  % (2033)------------------------------
% 4.22/0.94  % (2022)Time limit reached!
% 4.22/0.94  % (2022)------------------------------
% 4.22/0.94  % (2022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.94  % (2022)Termination reason: Time limit
% 4.22/0.94  
% 4.22/0.94  % (2022)Memory used [KB]: 9083
% 4.22/0.94  % (2022)Time elapsed: 0.504 s
% 4.22/0.94  % (2022)------------------------------
% 4.22/0.94  % (2022)------------------------------
% 4.22/0.94  % (2057)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.39/0.96  % (2047)Refutation found. Thanks to Tanya!
% 4.39/0.96  % SZS status Theorem for theBenchmark
% 4.39/0.96  % SZS output start Proof for theBenchmark
% 4.39/0.96  fof(f4845,plain,(
% 4.39/0.96    $false),
% 4.39/0.96    inference(avatar_sat_refutation,[],[f686,f690,f1226,f2297,f3315,f4759,f4844])).
% 4.39/0.96  fof(f4844,plain,(
% 4.39/0.96    spl29_1 | spl29_12),
% 4.39/0.96    inference(avatar_contradiction_clause,[],[f4843])).
% 4.39/0.96  fof(f4843,plain,(
% 4.39/0.96    $false | (spl29_1 | spl29_12)),
% 4.39/0.96    inference(subsumption_resolution,[],[f4762,f2296])).
% 4.39/0.96  fof(f2296,plain,(
% 4.39/0.96    ~r2_hidden(sK6(k1_tarski(sK0),sK0),sK0) | spl29_12),
% 4.39/0.96    inference(avatar_component_clause,[],[f2294])).
% 4.39/0.96  fof(f2294,plain,(
% 4.39/0.96    spl29_12 <=> r2_hidden(sK6(k1_tarski(sK0),sK0),sK0)),
% 4.39/0.96    introduced(avatar_definition,[new_symbols(naming,[spl29_12])])).
% 4.39/0.96  fof(f4762,plain,(
% 4.39/0.96    r2_hidden(sK6(k1_tarski(sK0),sK0),sK0) | (spl29_1 | spl29_12)),
% 4.39/0.96    inference(unit_resulting_resolution,[],[f677,f619,f297,f2296,f359])).
% 4.39/0.96  fof(f359,plain,(
% 4.39/0.96    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK6(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK6(X0,X1),X1) | k1_xboole_0 = X0) )),
% 4.39/0.96    inference(cnf_transformation,[],[f221])).
% 4.39/0.96  fof(f221,plain,(
% 4.39/0.96    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK6(X0,X1),sK7(X0,X1)) & r2_hidden(sK7(X0,X1),X0)) | ~r2_hidden(sK6(X0,X1),X1)) & (! [X4] : (r2_hidden(sK6(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK8(X0,X5)) & r2_hidden(sK8(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 4.39/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f217,f220,f219,f218])).
% 4.39/0.96  fof(f218,plain,(
% 4.39/0.96    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK6(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK6(X0,X1),X1)) & (! [X4] : (r2_hidden(sK6(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK6(X0,X1),X1))))),
% 4.39/0.96    introduced(choice_axiom,[])).
% 4.39/0.96  fof(f219,plain,(
% 4.39/0.96    ! [X1,X0] : (? [X3] : (~r2_hidden(sK6(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK6(X0,X1),sK7(X0,X1)) & r2_hidden(sK7(X0,X1),X0)))),
% 4.39/0.96    introduced(choice_axiom,[])).
% 4.39/0.96  fof(f220,plain,(
% 4.39/0.96    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK8(X0,X5)) & r2_hidden(sK8(X0,X5),X0)))),
% 4.39/0.96    introduced(choice_axiom,[])).
% 4.39/0.96  fof(f217,plain,(
% 4.39/0.96    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 4.39/0.96    inference(rectify,[],[f216])).
% 4.39/0.96  fof(f216,plain,(
% 4.39/0.96    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 4.39/0.96    inference(nnf_transformation,[],[f149])).
% 4.39/0.96  fof(f149,plain,(
% 4.39/0.96    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 4.39/0.96    inference(ennf_transformation,[],[f127])).
% 4.39/0.96  fof(f127,axiom,(
% 4.39/0.96    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 4.39/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 4.39/0.96  fof(f297,plain,(
% 4.39/0.96    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 4.39/0.96    inference(cnf_transformation,[],[f204])).
% 4.39/0.96  fof(f204,plain,(
% 4.39/0.96    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 4.39/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f144,f203])).
% 4.39/0.96  fof(f203,plain,(
% 4.39/0.96    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK0 != k1_setfam_1(k1_tarski(sK0))),
% 4.39/0.96    introduced(choice_axiom,[])).
% 4.39/0.96  fof(f144,plain,(
% 4.39/0.96    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 4.39/0.96    inference(ennf_transformation,[],[f139])).
% 4.39/0.96  fof(f139,negated_conjecture,(
% 4.39/0.96    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 4.39/0.96    inference(negated_conjecture,[],[f138])).
% 4.39/0.96  fof(f138,conjecture,(
% 4.39/0.96    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 4.39/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 4.39/0.96  fof(f619,plain,(
% 4.39/0.96    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 4.39/0.96    inference(equality_resolution,[],[f618])).
% 4.39/0.96  fof(f618,plain,(
% 4.39/0.96    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 4.39/0.96    inference(equality_resolution,[],[f418])).
% 4.39/0.96  fof(f418,plain,(
% 4.39/0.96    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 4.39/0.96    inference(cnf_transformation,[],[f257])).
% 4.39/0.96  fof(f257,plain,(
% 4.39/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK22(X0,X1) != X0 | ~r2_hidden(sK22(X0,X1),X1)) & (sK22(X0,X1) = X0 | r2_hidden(sK22(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.39/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f255,f256])).
% 4.39/0.96  fof(f256,plain,(
% 4.39/0.96    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK22(X0,X1) != X0 | ~r2_hidden(sK22(X0,X1),X1)) & (sK22(X0,X1) = X0 | r2_hidden(sK22(X0,X1),X1))))),
% 4.39/0.96    introduced(choice_axiom,[])).
% 4.39/0.96  fof(f255,plain,(
% 4.39/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.39/0.96    inference(rectify,[],[f254])).
% 4.39/0.96  fof(f254,plain,(
% 4.39/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 4.39/0.96    inference(nnf_transformation,[],[f76])).
% 4.39/0.96  fof(f76,axiom,(
% 4.39/0.96    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 4.39/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 4.39/0.96  fof(f677,plain,(
% 4.39/0.96    k1_xboole_0 != k1_tarski(sK0) | spl29_1),
% 4.39/0.96    inference(avatar_component_clause,[],[f676])).
% 4.39/0.96  fof(f676,plain,(
% 4.39/0.96    spl29_1 <=> k1_xboole_0 = k1_tarski(sK0)),
% 4.39/0.96    introduced(avatar_definition,[new_symbols(naming,[spl29_1])])).
% 4.39/0.96  fof(f4759,plain,(
% 4.39/0.96    ~spl29_12 | ~spl29_11 | spl29_14),
% 4.39/0.96    inference(avatar_split_clause,[],[f4714,f3312,f2290,f2294])).
% 4.39/0.96  fof(f2290,plain,(
% 4.39/0.96    spl29_11 <=> r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0))),
% 4.39/0.96    introduced(avatar_definition,[new_symbols(naming,[spl29_11])])).
% 4.39/0.96  fof(f3312,plain,(
% 4.39/0.96    spl29_14 <=> r2_hidden(sK6(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0))),
% 4.39/0.96    introduced(avatar_definition,[new_symbols(naming,[spl29_14])])).
% 4.39/0.96  fof(f4714,plain,(
% 4.39/0.96    ~r2_hidden(sK6(k1_tarski(sK0),sK0),sK0) | (~spl29_11 | spl29_14)),
% 4.39/0.96    inference(backward_demodulation,[],[f3314,f4617])).
% 4.39/0.96  fof(f4617,plain,(
% 4.39/0.96    sK0 = sK7(k1_tarski(sK0),sK0) | ~spl29_11),
% 4.39/0.96    inference(unit_resulting_resolution,[],[f2292,f620])).
% 4.39/0.96  fof(f620,plain,(
% 4.39/0.96    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 4.39/0.96    inference(equality_resolution,[],[f417])).
% 4.39/0.96  fof(f417,plain,(
% 4.39/0.96    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 4.39/0.96    inference(cnf_transformation,[],[f257])).
% 4.39/0.96  fof(f2292,plain,(
% 4.39/0.96    r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0)) | ~spl29_11),
% 4.39/0.96    inference(avatar_component_clause,[],[f2290])).
% 4.39/0.96  fof(f3314,plain,(
% 4.39/0.96    ~r2_hidden(sK6(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0)) | spl29_14),
% 4.39/0.96    inference(avatar_component_clause,[],[f3312])).
% 4.39/0.96  fof(f3315,plain,(
% 4.39/0.96    ~spl29_14 | ~spl29_12 | ~spl29_4),
% 4.39/0.96    inference(avatar_split_clause,[],[f2298,f688,f2294,f3312])).
% 4.39/0.96  fof(f688,plain,(
% 4.39/0.96    spl29_4 <=> ! [X3] : (sK0 != X3 | ~r2_hidden(sK6(k1_tarski(sK0),X3),X3) | ~r2_hidden(sK6(k1_tarski(sK0),X3),sK7(k1_tarski(sK0),X3)))),
% 4.39/0.96    introduced(avatar_definition,[new_symbols(naming,[spl29_4])])).
% 4.39/0.96  fof(f2298,plain,(
% 4.39/0.96    ~r2_hidden(sK6(k1_tarski(sK0),sK0),sK0) | ~r2_hidden(sK6(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0)) | ~spl29_4),
% 4.39/0.96    inference(equality_resolution,[],[f689])).
% 4.39/0.96  fof(f689,plain,(
% 4.39/0.96    ( ! [X3] : (sK0 != X3 | ~r2_hidden(sK6(k1_tarski(sK0),X3),X3) | ~r2_hidden(sK6(k1_tarski(sK0),X3),sK7(k1_tarski(sK0),X3))) ) | ~spl29_4),
% 4.39/0.96    inference(avatar_component_clause,[],[f688])).
% 4.39/0.96  fof(f2297,plain,(
% 4.39/0.96    spl29_11 | ~spl29_12 | ~spl29_3),
% 4.39/0.96    inference(avatar_split_clause,[],[f2288,f684,f2294,f2290])).
% 4.39/0.96  fof(f684,plain,(
% 4.39/0.96    spl29_3 <=> ! [X2] : (sK0 != X2 | ~r2_hidden(sK6(k1_tarski(sK0),X2),X2) | r2_hidden(sK7(k1_tarski(sK0),X2),k1_tarski(sK0)))),
% 4.39/0.96    introduced(avatar_definition,[new_symbols(naming,[spl29_3])])).
% 4.39/0.96  fof(f2288,plain,(
% 4.39/0.96    ~r2_hidden(sK6(k1_tarski(sK0),sK0),sK0) | r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0)) | ~spl29_3),
% 4.39/0.96    inference(equality_resolution,[],[f685])).
% 4.39/0.96  fof(f685,plain,(
% 4.39/0.96    ( ! [X2] : (sK0 != X2 | ~r2_hidden(sK6(k1_tarski(sK0),X2),X2) | r2_hidden(sK7(k1_tarski(sK0),X2),k1_tarski(sK0))) ) | ~spl29_3),
% 4.39/0.96    inference(avatar_component_clause,[],[f684])).
% 4.39/0.96  fof(f1226,plain,(
% 4.39/0.96    ~spl29_1),
% 4.39/0.96    inference(avatar_contradiction_clause,[],[f1225])).
% 4.39/0.96  fof(f1225,plain,(
% 4.39/0.96    $false | ~spl29_1),
% 4.39/0.96    inference(subsumption_resolution,[],[f1036,f602])).
% 4.39/0.96  fof(f602,plain,(
% 4.39/0.96    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 4.39/0.96    inference(equality_resolution,[],[f314])).
% 4.39/0.96  fof(f314,plain,(
% 4.39/0.96    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 4.39/0.96    inference(cnf_transformation,[],[f145])).
% 4.39/0.96  fof(f145,plain,(
% 4.39/0.96    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 4.39/0.96    inference(ennf_transformation,[],[f63])).
% 4.39/0.96  fof(f63,axiom,(
% 4.39/0.96    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 4.39/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 4.39/0.96  fof(f1036,plain,(
% 4.39/0.96    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl29_1),
% 4.39/0.96    inference(unit_resulting_resolution,[],[f972,f972,f368])).
% 4.39/0.96  fof(f368,plain,(
% 4.39/0.96    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.39/0.96    inference(cnf_transformation,[],[f225])).
% 4.39/0.96  fof(f225,plain,(
% 4.39/0.96    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.39/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f151,f224])).
% 4.39/0.96  fof(f224,plain,(
% 4.39/0.96    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)))),
% 4.39/0.96    introduced(choice_axiom,[])).
% 4.39/0.96  fof(f151,plain,(
% 4.39/0.96    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.39/0.96    inference(ennf_transformation,[],[f143])).
% 4.39/0.96  fof(f143,plain,(
% 4.39/0.96    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.39/0.96    inference(rectify,[],[f12])).
% 4.39/0.96  fof(f12,axiom,(
% 4.39/0.96    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.39/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 4.39/0.96  fof(f972,plain,(
% 4.39/0.96    r2_hidden(sK0,k1_xboole_0) | ~spl29_1),
% 4.39/0.96    inference(forward_demodulation,[],[f971,f304])).
% 4.39/0.96  fof(f304,plain,(
% 4.39/0.96    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 4.39/0.96    inference(cnf_transformation,[],[f53])).
% 4.39/0.96  fof(f53,axiom,(
% 4.39/0.96    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 4.39/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 4.39/0.96  fof(f971,plain,(
% 4.39/0.96    r2_hidden(sK0,k4_xboole_0(k1_xboole_0,k1_tarski(k1_xboole_0))) | ~spl29_1),
% 4.39/0.96    inference(forward_demodulation,[],[f958,f678])).
% 4.39/0.96  fof(f678,plain,(
% 4.39/0.96    k1_xboole_0 = k1_tarski(sK0) | ~spl29_1),
% 4.39/0.96    inference(avatar_component_clause,[],[f676])).
% 4.39/0.96  fof(f958,plain,(
% 4.39/0.96    r2_hidden(sK0,k4_xboole_0(k1_tarski(sK0),k1_tarski(k1_xboole_0))) | ~spl29_1),
% 4.39/0.96    inference(unit_resulting_resolution,[],[f619,f895,f506])).
% 4.39/0.96  fof(f506,plain,(
% 4.39/0.96    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 4.39/0.96    inference(cnf_transformation,[],[f292])).
% 4.39/0.96  fof(f292,plain,(
% 4.39/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 4.39/0.96    inference(flattening,[],[f291])).
% 4.39/0.96  fof(f291,plain,(
% 4.39/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 4.39/0.96    inference(nnf_transformation,[],[f104])).
% 4.39/0.96  fof(f104,axiom,(
% 4.39/0.96    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 4.39/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 4.39/0.96  fof(f895,plain,(
% 4.39/0.96    k1_xboole_0 != sK0 | ~spl29_1),
% 4.39/0.96    inference(forward_demodulation,[],[f822,f298])).
% 4.39/0.96  fof(f298,plain,(
% 4.39/0.96    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 4.39/0.96    inference(cnf_transformation,[],[f130])).
% 4.39/0.96  fof(f130,axiom,(
% 4.39/0.96    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 4.39/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_setfam_1)).
% 4.39/0.96  fof(f822,plain,(
% 4.39/0.96    k1_setfam_1(k1_xboole_0) != sK0 | ~spl29_1),
% 4.39/0.96    inference(backward_demodulation,[],[f297,f678])).
% 4.39/0.96  fof(f690,plain,(
% 4.39/0.96    spl29_1 | spl29_4),
% 4.39/0.96    inference(avatar_split_clause,[],[f673,f688,f676])).
% 4.39/0.96  fof(f673,plain,(
% 4.39/0.96    ( ! [X3] : (sK0 != X3 | ~r2_hidden(sK6(k1_tarski(sK0),X3),sK7(k1_tarski(sK0),X3)) | ~r2_hidden(sK6(k1_tarski(sK0),X3),X3) | k1_xboole_0 = k1_tarski(sK0)) )),
% 4.39/0.96    inference(superposition,[],[f297,f361])).
% 4.39/0.96  fof(f361,plain,(
% 4.39/0.96    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK6(X0,X1),sK7(X0,X1)) | ~r2_hidden(sK6(X0,X1),X1) | k1_xboole_0 = X0) )),
% 4.39/0.96    inference(cnf_transformation,[],[f221])).
% 4.39/0.96  fof(f686,plain,(
% 4.39/0.96    spl29_1 | spl29_3),
% 4.39/0.96    inference(avatar_split_clause,[],[f672,f684,f676])).
% 4.39/0.96  fof(f672,plain,(
% 4.39/0.96    ( ! [X2] : (sK0 != X2 | r2_hidden(sK7(k1_tarski(sK0),X2),k1_tarski(sK0)) | ~r2_hidden(sK6(k1_tarski(sK0),X2),X2) | k1_xboole_0 = k1_tarski(sK0)) )),
% 4.39/0.96    inference(superposition,[],[f297,f360])).
% 4.39/0.96  fof(f360,plain,(
% 4.39/0.96    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK7(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1) | k1_xboole_0 = X0) )),
% 4.39/0.96    inference(cnf_transformation,[],[f221])).
% 4.39/0.96  % SZS output end Proof for theBenchmark
% 4.39/0.96  % (2047)------------------------------
% 4.39/0.96  % (2047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.96  % (2047)Termination reason: Refutation
% 4.39/0.96  
% 4.39/0.96  % (2047)Memory used [KB]: 13944
% 4.39/0.96  % (2047)Time elapsed: 0.543 s
% 4.39/0.96  % (2047)------------------------------
% 4.39/0.96  % (2047)------------------------------
% 4.39/0.96  % (2020)Success in time 0.6 s
%------------------------------------------------------------------------------
