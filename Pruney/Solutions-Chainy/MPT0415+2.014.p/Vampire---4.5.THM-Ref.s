%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 314 expanded)
%              Number of leaves         :   13 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  349 (1377 expanded)
%              Number of equality atoms :   61 ( 466 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f750,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f355,f411,f590,f749])).

fof(f749,plain,
    ( ~ spl4_6
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | ~ spl4_6
    | spl4_12 ),
    inference(subsumption_resolution,[],[f741,f350])).

fof(f350,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl4_6
  <=> r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f741,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)
    | spl4_12 ),
    inference(resolution,[],[f500,f145])).

fof(f145,plain,(
    ! [X5] :
      ( r2_hidden(X5,sK1)
      | ~ r2_hidden(X5,k1_xboole_0) ) ),
    inference(superposition,[],[f55,f83])).

fof(f83,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f65,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f65,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f30,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f500,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl4_12
  <=> r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f590,plain,
    ( ~ spl4_12
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f589,f352,f499])).

fof(f352,plain,
    ( spl4_7
  <=> r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f589,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    inference(subsumption_resolution,[],[f583,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f583,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f97,f30])).

fof(f97,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X2)),sK1)
      | ~ r2_hidden(sK2(sK0,sK1,X2),X2)
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f86,f30])).

fof(f86,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X2)),sK1)
      | ~ r2_hidden(sK2(sK0,sK1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f32,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | r2_hidden(sK2(X0,X1,X2),X2) )
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f32,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f411,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f409,f30])).

fof(f409,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_7 ),
    inference(forward_demodulation,[],[f408,f101])).

fof(f101,plain,(
    sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f90,f30])).

fof(f90,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f38,f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f408,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_7 ),
    inference(subsumption_resolution,[],[f407,f366])).

fof(f366,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f365,f31])).

fof(f365,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl4_7 ),
    inference(forward_demodulation,[],[f364,f32])).

fof(f364,plain,
    ( sK1 = k7_setfam_1(sK0,sK1)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f363,f30])).

fof(f363,plain,
    ( sK1 = k7_setfam_1(sK0,sK1)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_7 ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,
    ( sK1 = k7_setfam_1(sK0,sK1)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_7 ),
    inference(resolution,[],[f354,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f354,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f352])).

fof(f407,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_7 ),
    inference(forward_demodulation,[],[f406,f101])).

fof(f406,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k7_setfam_1(sK0,k1_xboole_0))
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_7 ),
    inference(subsumption_resolution,[],[f405,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f405,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k7_setfam_1(sK0,k1_xboole_0))
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_7 ),
    inference(subsumption_resolution,[],[f402,f341])).

fof(f341,plain,(
    m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f336,f31])).

fof(f336,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f95,f30])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f84,f30])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f32,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f402,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k7_setfam_1(sK0,k1_xboole_0))
    | ~ m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_7 ),
    inference(resolution,[],[f360,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f360,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),k1_xboole_0)
    | spl4_7 ),
    inference(resolution,[],[f354,f145])).

fof(f355,plain,
    ( spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f342,f352,f348])).

fof(f342,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) ),
    inference(resolution,[],[f341,f103])).

fof(f103,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(k3_subset_1(sK0,X3),sK1)
      | r2_hidden(X3,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f102,f30])).

fof(f102,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(k3_subset_1(sK0,X3),sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f91,f47])).

fof(f91,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(k3_subset_1(sK0,X3),sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f51,f32])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:49:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (8533)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (8524)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (8525)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (8532)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (8530)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (8530)Refutation not found, incomplete strategy% (8530)------------------------------
% 0.21/0.52  % (8530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8538)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (8530)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8530)Memory used [KB]: 10618
% 0.21/0.53  % (8530)Time elapsed: 0.087 s
% 0.21/0.53  % (8530)------------------------------
% 0.21/0.53  % (8530)------------------------------
% 0.21/0.53  % (8521)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.54  % (8523)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.54  % (8520)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (8522)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (8534)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.54  % (8538)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f750,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f355,f411,f590,f749])).
% 0.21/0.54  fof(f749,plain,(
% 0.21/0.54    ~spl4_6 | spl4_12),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f748])).
% 0.21/0.54  fof(f748,plain,(
% 0.21/0.54    $false | (~spl4_6 | spl4_12)),
% 0.21/0.54    inference(subsumption_resolution,[],[f741,f350])).
% 0.21/0.54  fof(f350,plain,(
% 0.21/0.54    r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) | ~spl4_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f348])).
% 0.21/0.54  fof(f348,plain,(
% 0.21/0.54    spl4_6 <=> r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.54  fof(f741,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) | spl4_12),
% 0.21/0.54    inference(resolution,[],[f500,f145])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X5] : (r2_hidden(X5,sK1) | ~r2_hidden(X5,k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f55,f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(resolution,[],[f65,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(resolution,[],[f30,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(flattening,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f8])).
% 0.21/0.54  fof(f8,conjecture,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(rectify,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.54  fof(f500,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | spl4_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f499])).
% 0.21/0.54  fof(f499,plain,(
% 0.21/0.54    spl4_12 <=> r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.54  fof(f590,plain,(
% 0.21/0.54    ~spl4_12 | ~spl4_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f589,f352,f499])).
% 0.21/0.54  fof(f352,plain,(
% 0.21/0.54    spl4_7 <=> r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f589,plain,(
% 0.21/0.54    ~r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | ~r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f583,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    k1_xboole_0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f583,plain,(
% 0.21/0.54    ~r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 0.21/0.54    inference(resolution,[],[f97,f30])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X2)),sK1) | ~r2_hidden(sK2(sK0,sK1,X2),X2) | k1_xboole_0 = X2) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f86,f30])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X2)),sK1) | ~r2_hidden(sK2(sK0,sK1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.54    inference(superposition,[],[f32,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | ~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(rectify,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(nnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f411,plain,(
% 0.21/0.54    spl4_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f410])).
% 0.21/0.54  fof(f410,plain,(
% 0.21/0.54    $false | spl4_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f409,f30])).
% 0.21/0.54  fof(f409,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_7),
% 0.21/0.54    inference(forward_demodulation,[],[f408,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    sK1 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f90,f30])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    sK1 = k7_setfam_1(sK0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(superposition,[],[f38,f32])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.21/0.54  fof(f408,plain,(
% 0.21/0.54    ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f407,f366])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    r2_hidden(sK2(sK0,sK1,sK1),sK1) | spl4_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f365,f31])).
% 0.21/0.54  fof(f365,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | r2_hidden(sK2(sK0,sK1,sK1),sK1) | spl4_7),
% 0.21/0.54    inference(forward_demodulation,[],[f364,f32])).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    sK1 = k7_setfam_1(sK0,sK1) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | spl4_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f363,f30])).
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    sK1 = k7_setfam_1(sK0,sK1) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_7),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f358])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    sK1 = k7_setfam_1(sK0,sK1) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_7),
% 0.21/0.54    inference(resolution,[],[f354,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f354,plain,(
% 0.21/0.54    ~r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f352])).
% 0.21/0.54  fof(f407,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_7),
% 0.21/0.54    inference(forward_demodulation,[],[f406,f101])).
% 0.21/0.54  fof(f406,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK0,sK1,sK1),k7_setfam_1(sK0,k1_xboole_0)) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f405,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.54  fof(f405,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK0,sK1,sK1),k7_setfam_1(sK0,k1_xboole_0)) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f402,f341])).
% 0.21/0.54  fof(f341,plain,(
% 0.21/0.54    m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f336,f31])).
% 0.21/0.54  fof(f336,plain,(
% 0.21/0.54    m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) | k1_xboole_0 = sK1),
% 0.21/0.54    inference(resolution,[],[f95,f30])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f84,f30])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.54    inference(superposition,[],[f32,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f402,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK0,sK1,sK1),k7_setfam_1(sK0,k1_xboole_0)) | ~m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_7),
% 0.21/0.54    inference(resolution,[],[f360,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X4,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    ~r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),k1_xboole_0) | spl4_7),
% 0.21/0.54    inference(resolution,[],[f354,f145])).
% 0.21/0.54  fof(f355,plain,(
% 0.21/0.54    spl4_6 | ~spl4_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f342,f352,f348])).
% 0.21/0.54  fof(f342,plain,(
% 0.21/0.54    ~r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)),
% 0.21/0.54    inference(resolution,[],[f341,f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(k3_subset_1(sK0,X3),sK1) | r2_hidden(X3,k1_xboole_0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f102,f30])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(k3_subset_1(sK0,X3),sK1) | ~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f91,f47])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(k3_subset_1(sK0,X3),sK1) | ~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.54    inference(superposition,[],[f51,f32])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k7_setfam_1(X0,X1)) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (8538)------------------------------
% 0.21/0.54  % (8538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8538)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (8538)Memory used [KB]: 6396
% 0.21/0.54  % (8538)Time elapsed: 0.104 s
% 0.21/0.54  % (8538)------------------------------
% 0.21/0.54  % (8538)------------------------------
% 0.21/0.55  % (8518)Success in time 0.181 s
%------------------------------------------------------------------------------
