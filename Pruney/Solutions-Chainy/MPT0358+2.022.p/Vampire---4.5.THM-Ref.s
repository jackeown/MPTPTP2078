%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:31 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  141 (1243 expanded)
%              Number of leaves         :   22 ( 321 expanded)
%              Depth                    :   21
%              Number of atoms          :  482 (5189 expanded)
%              Number of equality atoms :  100 (1123 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f221,f224,f337])).

fof(f337,plain,
    ( spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f329,f104])).

fof(f104,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f329,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_3 ),
    inference(resolution,[],[f325,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f325,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f324,f307])).

fof(f307,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f306,f260])).

fof(f260,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | r2_hidden(X2,sK1) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f248,f239])).

fof(f239,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f236,f238])).

fof(f238,plain,
    ( sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f109,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f109,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_3
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f236,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(resolution,[],[f109,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f63,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f248,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k5_xboole_0(sK1,sK1))
      | r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f92,f234])).

fof(f234,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f230,f56])).

fof(f230,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f229,f89])).

fof(f89,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f229,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f227,f46])).

fof(f46,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f227,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f43,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k1_subset_1(sK0)
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( sK1 = k1_subset_1(sK0)
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f51])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f306,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f300,f264])).

fof(f264,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f261,f263])).

fof(f263,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f257,f56])).

fof(f257,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f244,f239])).

fof(f244,plain,(
    r1_tarski(k5_xboole_0(sK1,sK1),sK1) ),
    inference(superposition,[],[f78,f234])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f261,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f257,f80])).

fof(f300,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_3 ),
    inference(superposition,[],[f91,f263])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f51])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f324,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f323,f239])).

fof(f323,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k5_xboole_0(sK1,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f316,f283])).

fof(f283,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(sK0,sK1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f91,f240])).

fof(f240,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f234,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f316,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k5_xboole_0(sK1,sK1))
        | r2_hidden(X0,k5_xboole_0(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_3 ),
    inference(superposition,[],[f90,f254])).

fof(f254,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f238,f253])).

fof(f253,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f226,f240])).

fof(f226,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f43,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f51])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f66,f51])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f224,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f100,f213])).

fof(f213,plain,
    ( ! [X3] : r1_tarski(k1_xboole_0,X3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f204,f123])).

fof(f123,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f120,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f118,f56])).

fof(f118,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f117,f89])).

fof(f117,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f114,f46])).

fof(f114,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f112,f52])).

fof(f112,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f43,f103])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f120,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f118,f80])).

fof(f204,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
        | r1_tarski(k1_xboole_0,X3) )
    | ~ spl6_2 ),
    inference(superposition,[],[f81,f181])).

fof(f181,plain,
    ( ! [X9] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X9)
    | ~ spl6_2 ),
    inference(resolution,[],[f146,f138])).

fof(f138,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_xboole_0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f132,f136])).

fof(f136,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f129,f123])).

fof(f129,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl6_2 ),
    inference(superposition,[],[f91,f122])).

fof(f132,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | r2_hidden(X4,sK0) )
    | ~ spl6_2 ),
    inference(superposition,[],[f94,f122])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f146,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK5(X4,X5,k1_xboole_0),X4)
        | k1_xboole_0 = k3_xboole_0(X4,X5) )
    | ~ spl6_2 ),
    inference(resolution,[],[f138,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f51])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f100,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_1
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f221,plain,
    ( ~ spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl6_2
    | spl6_3 ),
    inference(resolution,[],[f213,f125])).

fof(f125,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0))
    | ~ spl6_2
    | spl6_3 ),
    inference(backward_demodulation,[],[f111,f124])).

fof(f124,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f116,f122])).

fof(f116,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK0))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f113,f50])).

fof(f113,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0))
    | ~ spl6_2 ),
    inference(resolution,[],[f112,f79])).

fof(f111,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | ~ spl6_2
    | spl6_3 ),
    inference(backward_demodulation,[],[f108,f103])).

fof(f108,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f110,plain,
    ( spl6_3
    | spl6_2 ),
    inference(avatar_split_clause,[],[f77,f102,f107])).

fof(f77,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f44,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f105,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f96,f102,f98])).

fof(f96,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f76])).

fof(f76,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:15:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (19512)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.45  % (19496)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (19491)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (19487)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19486)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (19488)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (19505)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (19485)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (19497)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.52  % (19500)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.52  % (19501)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.28/0.52  % (19490)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.52  % (19507)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.28/0.52  % (19502)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.52  % (19505)Refutation not found, incomplete strategy% (19505)------------------------------
% 1.28/0.52  % (19505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (19505)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (19505)Memory used [KB]: 10746
% 1.28/0.52  % (19505)Time elapsed: 0.078 s
% 1.28/0.52  % (19505)------------------------------
% 1.28/0.52  % (19505)------------------------------
% 1.28/0.52  % (19495)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.52  % (19483)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.52  % (19489)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.52  % (19492)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.52  % (19493)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.28/0.52  % (19491)Refutation found. Thanks to Tanya!
% 1.28/0.52  % SZS status Theorem for theBenchmark
% 1.28/0.52  % SZS output start Proof for theBenchmark
% 1.28/0.52  fof(f338,plain,(
% 1.28/0.52    $false),
% 1.28/0.52    inference(avatar_sat_refutation,[],[f105,f110,f221,f224,f337])).
% 1.28/0.52  fof(f337,plain,(
% 1.28/0.52    spl6_2 | ~spl6_3),
% 1.28/0.52    inference(avatar_contradiction_clause,[],[f336])).
% 1.28/0.52  fof(f336,plain,(
% 1.28/0.52    $false | (spl6_2 | ~spl6_3)),
% 1.28/0.52    inference(subsumption_resolution,[],[f329,f104])).
% 1.28/0.52  fof(f104,plain,(
% 1.28/0.52    k1_xboole_0 != sK1 | spl6_2),
% 1.28/0.52    inference(avatar_component_clause,[],[f102])).
% 1.28/0.52  fof(f102,plain,(
% 1.28/0.52    spl6_2 <=> k1_xboole_0 = sK1),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.28/0.52  fof(f329,plain,(
% 1.28/0.52    k1_xboole_0 = sK1 | ~spl6_3),
% 1.28/0.52    inference(resolution,[],[f325,f48])).
% 1.28/0.52  fof(f48,plain,(
% 1.28/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.28/0.52    inference(cnf_transformation,[],[f26])).
% 1.28/0.52  fof(f26,plain,(
% 1.28/0.52    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.28/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f25])).
% 1.28/0.52  fof(f25,plain,(
% 1.28/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.28/0.52    introduced(choice_axiom,[])).
% 1.28/0.52  fof(f17,plain,(
% 1.28/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.28/0.52    inference(ennf_transformation,[],[f4])).
% 1.28/0.52  fof(f4,axiom,(
% 1.28/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.28/0.52  fof(f325,plain,(
% 1.28/0.52    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 1.28/0.52    inference(subsumption_resolution,[],[f324,f307])).
% 1.28/0.52  fof(f307,plain,(
% 1.28/0.52    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_3),
% 1.28/0.52    inference(subsumption_resolution,[],[f306,f260])).
% 1.28/0.52  fof(f260,plain,(
% 1.28/0.52    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,sK1)) ) | ~spl6_3),
% 1.28/0.52    inference(forward_demodulation,[],[f248,f239])).
% 1.28/0.52  fof(f239,plain,(
% 1.28/0.52    k1_xboole_0 = k5_xboole_0(sK1,sK1) | ~spl6_3),
% 1.28/0.52    inference(backward_demodulation,[],[f236,f238])).
% 1.28/0.52  fof(f238,plain,(
% 1.28/0.52    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl6_3),
% 1.28/0.52    inference(resolution,[],[f109,f56])).
% 1.28/0.52  fof(f56,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.28/0.52    inference(cnf_transformation,[],[f19])).
% 1.28/0.52  fof(f19,plain,(
% 1.28/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.28/0.52    inference(ennf_transformation,[],[f7])).
% 1.28/0.52  fof(f7,axiom,(
% 1.28/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.28/0.52  fof(f109,plain,(
% 1.28/0.52    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl6_3),
% 1.28/0.52    inference(avatar_component_clause,[],[f107])).
% 1.28/0.52  fof(f107,plain,(
% 1.28/0.52    spl6_3 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.28/0.52  fof(f236,plain,(
% 1.28/0.52    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1))) | ~spl6_3),
% 1.28/0.52    inference(resolution,[],[f109,f80])).
% 1.28/0.52  fof(f80,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.28/0.52    inference(definition_unfolding,[],[f63,f51])).
% 1.28/0.52  fof(f51,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f6])).
% 1.28/0.52  fof(f6,axiom,(
% 1.28/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.28/0.52  fof(f63,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f32])).
% 1.28/0.52  fof(f32,plain,(
% 1.28/0.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.28/0.52    inference(nnf_transformation,[],[f5])).
% 1.28/0.52  fof(f5,axiom,(
% 1.28/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.28/0.52  fof(f248,plain,(
% 1.28/0.52    ( ! [X2] : (~r2_hidden(X2,k5_xboole_0(sK1,sK1)) | r2_hidden(X2,sK1)) )),
% 1.28/0.52    inference(superposition,[],[f92,f234])).
% 1.28/0.52  fof(f234,plain,(
% 1.28/0.52    sK1 = k3_xboole_0(sK1,sK0)),
% 1.28/0.52    inference(resolution,[],[f230,f56])).
% 1.28/0.52  fof(f230,plain,(
% 1.28/0.52    r1_tarski(sK1,sK0)),
% 1.28/0.52    inference(resolution,[],[f229,f89])).
% 1.28/0.52  fof(f89,plain,(
% 1.28/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.28/0.52    inference(equality_resolution,[],[f58])).
% 1.28/0.52  fof(f58,plain,(
% 1.28/0.52    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.28/0.52    inference(cnf_transformation,[],[f31])).
% 1.28/0.52  fof(f31,plain,(
% 1.28/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.28/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.28/0.52  fof(f30,plain,(
% 1.28/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.28/0.52    introduced(choice_axiom,[])).
% 1.28/0.52  fof(f29,plain,(
% 1.28/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.28/0.52    inference(rectify,[],[f28])).
% 1.28/0.52  fof(f28,plain,(
% 1.28/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.28/0.52    inference(nnf_transformation,[],[f9])).
% 1.28/0.52  fof(f9,axiom,(
% 1.28/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.28/0.52  fof(f229,plain,(
% 1.28/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.28/0.52    inference(subsumption_resolution,[],[f227,f46])).
% 1.28/0.52  fof(f46,plain,(
% 1.28/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f13])).
% 1.28/0.52  fof(f13,axiom,(
% 1.28/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.28/0.52  fof(f227,plain,(
% 1.28/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.28/0.52    inference(resolution,[],[f43,f52])).
% 1.28/0.52  fof(f52,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f27])).
% 1.28/0.52  fof(f27,plain,(
% 1.28/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.28/0.52    inference(nnf_transformation,[],[f18])).
% 1.28/0.52  fof(f18,plain,(
% 1.28/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.28/0.52    inference(ennf_transformation,[],[f10])).
% 1.28/0.52  fof(f10,axiom,(
% 1.28/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.28/0.52  fof(f43,plain,(
% 1.28/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.28/0.52    inference(cnf_transformation,[],[f24])).
% 1.28/0.52  fof(f24,plain,(
% 1.28/0.52    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.28/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.28/0.52  fof(f23,plain,(
% 1.28/0.52    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.28/0.52    introduced(choice_axiom,[])).
% 1.28/0.52  fof(f22,plain,(
% 1.28/0.52    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.52    inference(flattening,[],[f21])).
% 1.28/0.52  fof(f21,plain,(
% 1.28/0.52    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.52    inference(nnf_transformation,[],[f16])).
% 1.28/0.52  fof(f16,plain,(
% 1.28/0.52    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.52    inference(ennf_transformation,[],[f15])).
% 1.28/0.52  fof(f15,negated_conjecture,(
% 1.28/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.28/0.52    inference(negated_conjecture,[],[f14])).
% 1.28/0.52  fof(f14,conjecture,(
% 1.28/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 1.28/0.52  fof(f92,plain,(
% 1.28/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 1.28/0.52    inference(equality_resolution,[],[f87])).
% 1.28/0.52  fof(f87,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.28/0.52    inference(definition_unfolding,[],[f64,f51])).
% 1.28/0.52  fof(f64,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.28/0.52    inference(cnf_transformation,[],[f37])).
% 1.28/0.52  fof(f37,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 1.28/0.52  fof(f36,plain,(
% 1.28/0.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.28/0.52    introduced(choice_axiom,[])).
% 1.28/0.52  fof(f35,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(rectify,[],[f34])).
% 1.28/0.52  fof(f34,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(flattening,[],[f33])).
% 1.28/0.52  fof(f33,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(nnf_transformation,[],[f3])).
% 1.28/0.52  fof(f3,axiom,(
% 1.28/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.28/0.52  fof(f306,plain,(
% 1.28/0.52    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,sK1)) ) | ~spl6_3),
% 1.28/0.52    inference(forward_demodulation,[],[f300,f264])).
% 1.28/0.52  fof(f264,plain,(
% 1.28/0.52    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl6_3),
% 1.28/0.52    inference(backward_demodulation,[],[f261,f263])).
% 1.28/0.52  fof(f263,plain,(
% 1.28/0.52    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | ~spl6_3),
% 1.28/0.52    inference(resolution,[],[f257,f56])).
% 1.28/0.52  fof(f257,plain,(
% 1.28/0.52    r1_tarski(k1_xboole_0,sK1) | ~spl6_3),
% 1.28/0.52    inference(forward_demodulation,[],[f244,f239])).
% 1.28/0.52  fof(f244,plain,(
% 1.28/0.52    r1_tarski(k5_xboole_0(sK1,sK1),sK1)),
% 1.28/0.52    inference(superposition,[],[f78,f234])).
% 1.28/0.52  fof(f78,plain,(
% 1.28/0.52    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.28/0.52    inference(definition_unfolding,[],[f49,f51])).
% 1.28/0.52  fof(f49,plain,(
% 1.28/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f8])).
% 1.28/0.52  fof(f8,axiom,(
% 1.28/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.28/0.52  fof(f261,plain,(
% 1.28/0.52    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) | ~spl6_3),
% 1.28/0.52    inference(resolution,[],[f257,f80])).
% 1.28/0.52  fof(f300,plain,(
% 1.28/0.52    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X1,sK1)) ) | ~spl6_3),
% 1.28/0.52    inference(superposition,[],[f91,f263])).
% 1.28/0.52  fof(f91,plain,(
% 1.28/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.28/0.52    inference(equality_resolution,[],[f86])).
% 1.28/0.52  fof(f86,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.28/0.52    inference(definition_unfolding,[],[f65,f51])).
% 1.28/0.52  fof(f65,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.28/0.52    inference(cnf_transformation,[],[f37])).
% 1.28/0.52  fof(f324,plain,(
% 1.28/0.52    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 1.28/0.52    inference(forward_demodulation,[],[f323,f239])).
% 1.28/0.52  fof(f323,plain,(
% 1.28/0.52    ( ! [X0] : (r2_hidden(X0,k5_xboole_0(sK1,sK1)) | ~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 1.28/0.52    inference(subsumption_resolution,[],[f316,f283])).
% 1.28/0.52  fof(f283,plain,(
% 1.28/0.52    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(sK0,sK1)) | ~r2_hidden(X1,sK1)) )),
% 1.28/0.52    inference(superposition,[],[f91,f240])).
% 1.28/0.52  fof(f240,plain,(
% 1.28/0.52    sK1 = k3_xboole_0(sK0,sK1)),
% 1.28/0.52    inference(superposition,[],[f234,f50])).
% 1.28/0.52  fof(f50,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f1])).
% 1.28/0.52  fof(f1,axiom,(
% 1.28/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.28/0.52  fof(f316,plain,(
% 1.28/0.52    ( ! [X0] : (r2_hidden(X0,k5_xboole_0(sK1,sK1)) | r2_hidden(X0,k5_xboole_0(sK0,sK1)) | ~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 1.28/0.52    inference(superposition,[],[f90,f254])).
% 1.28/0.52  fof(f254,plain,(
% 1.28/0.52    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl6_3),
% 1.28/0.52    inference(backward_demodulation,[],[f238,f253])).
% 1.28/0.52  fof(f253,plain,(
% 1.28/0.52    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.28/0.52    inference(backward_demodulation,[],[f226,f240])).
% 1.28/0.52  fof(f226,plain,(
% 1.28/0.52    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.28/0.52    inference(resolution,[],[f43,f79])).
% 1.28/0.52  fof(f79,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.28/0.52    inference(definition_unfolding,[],[f57,f51])).
% 1.28/0.52  fof(f57,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f20])).
% 1.28/0.52  fof(f20,plain,(
% 1.28/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.52    inference(ennf_transformation,[],[f12])).
% 1.28/0.52  fof(f12,axiom,(
% 1.28/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.28/0.52  fof(f90,plain,(
% 1.28/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.28/0.52    inference(equality_resolution,[],[f85])).
% 1.28/0.52  fof(f85,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.28/0.52    inference(definition_unfolding,[],[f66,f51])).
% 1.28/0.52  fof(f66,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.28/0.52    inference(cnf_transformation,[],[f37])).
% 1.28/0.52  fof(f224,plain,(
% 1.28/0.52    spl6_1 | ~spl6_2),
% 1.28/0.52    inference(avatar_contradiction_clause,[],[f223])).
% 1.28/0.52  fof(f223,plain,(
% 1.28/0.52    $false | (spl6_1 | ~spl6_2)),
% 1.28/0.52    inference(subsumption_resolution,[],[f100,f213])).
% 1.28/0.52  fof(f213,plain,(
% 1.28/0.52    ( ! [X3] : (r1_tarski(k1_xboole_0,X3)) ) | ~spl6_2),
% 1.28/0.52    inference(subsumption_resolution,[],[f204,f123])).
% 1.28/0.52  fof(f123,plain,(
% 1.28/0.52    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl6_2),
% 1.28/0.52    inference(backward_demodulation,[],[f120,f122])).
% 1.28/0.52  fof(f122,plain,(
% 1.28/0.52    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) | ~spl6_2),
% 1.28/0.52    inference(resolution,[],[f118,f56])).
% 1.28/0.52  fof(f118,plain,(
% 1.28/0.52    r1_tarski(k1_xboole_0,sK0) | ~spl6_2),
% 1.28/0.52    inference(resolution,[],[f117,f89])).
% 1.28/0.52  fof(f117,plain,(
% 1.28/0.52    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl6_2),
% 1.28/0.52    inference(subsumption_resolution,[],[f114,f46])).
% 1.28/0.52  fof(f114,plain,(
% 1.28/0.52    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl6_2),
% 1.28/0.52    inference(resolution,[],[f112,f52])).
% 1.28/0.52  fof(f112,plain,(
% 1.28/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl6_2),
% 1.28/0.52    inference(backward_demodulation,[],[f43,f103])).
% 1.28/0.52  fof(f103,plain,(
% 1.28/0.52    k1_xboole_0 = sK1 | ~spl6_2),
% 1.28/0.52    inference(avatar_component_clause,[],[f102])).
% 1.28/0.52  fof(f120,plain,(
% 1.28/0.52    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0)) | ~spl6_2),
% 1.28/0.52    inference(resolution,[],[f118,f80])).
% 1.28/0.52  fof(f204,plain,(
% 1.28/0.52    ( ! [X3] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | r1_tarski(k1_xboole_0,X3)) ) | ~spl6_2),
% 1.28/0.52    inference(superposition,[],[f81,f181])).
% 1.28/0.52  fof(f181,plain,(
% 1.28/0.52    ( ! [X9] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X9)) ) | ~spl6_2),
% 1.28/0.52    inference(resolution,[],[f146,f138])).
% 1.28/0.52  fof(f138,plain,(
% 1.28/0.52    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) ) | ~spl6_2),
% 1.28/0.52    inference(subsumption_resolution,[],[f132,f136])).
% 1.28/0.52  fof(f136,plain,(
% 1.28/0.52    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_2),
% 1.28/0.52    inference(forward_demodulation,[],[f129,f123])).
% 1.28/0.52  fof(f129,plain,(
% 1.28/0.52    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X1,sK0)) ) | ~spl6_2),
% 1.28/0.52    inference(superposition,[],[f91,f122])).
% 1.28/0.52  fof(f132,plain,(
% 1.28/0.52    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | r2_hidden(X4,sK0)) ) | ~spl6_2),
% 1.28/0.52    inference(superposition,[],[f94,f122])).
% 1.28/0.52  fof(f94,plain,(
% 1.28/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 1.28/0.52    inference(equality_resolution,[],[f71])).
% 1.28/0.52  fof(f71,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.28/0.52    inference(cnf_transformation,[],[f42])).
% 1.28/0.52  fof(f42,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 1.28/0.52  fof(f41,plain,(
% 1.28/0.52    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.28/0.52    introduced(choice_axiom,[])).
% 1.28/0.52  fof(f40,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(rectify,[],[f39])).
% 1.28/0.52  fof(f39,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(flattening,[],[f38])).
% 1.28/0.52  fof(f38,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(nnf_transformation,[],[f2])).
% 1.28/0.52  fof(f2,axiom,(
% 1.28/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.28/0.52  fof(f146,plain,(
% 1.28/0.52    ( ! [X4,X5] : (r2_hidden(sK5(X4,X5,k1_xboole_0),X4) | k1_xboole_0 = k3_xboole_0(X4,X5)) ) | ~spl6_2),
% 1.28/0.52    inference(resolution,[],[f138,f73])).
% 1.28/0.52  fof(f73,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 1.28/0.52    inference(cnf_transformation,[],[f42])).
% 1.28/0.52  fof(f81,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.28/0.52    inference(definition_unfolding,[],[f62,f51])).
% 1.28/0.52  fof(f62,plain,(
% 1.28/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.28/0.52    inference(cnf_transformation,[],[f32])).
% 1.28/0.52  fof(f100,plain,(
% 1.28/0.52    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | spl6_1),
% 1.28/0.52    inference(avatar_component_clause,[],[f98])).
% 1.28/0.52  fof(f98,plain,(
% 1.28/0.52    spl6_1 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.28/0.52  fof(f221,plain,(
% 1.28/0.52    ~spl6_2 | spl6_3),
% 1.28/0.52    inference(avatar_contradiction_clause,[],[f217])).
% 1.28/0.52  fof(f217,plain,(
% 1.28/0.52    $false | (~spl6_2 | spl6_3)),
% 1.28/0.52    inference(resolution,[],[f213,f125])).
% 1.28/0.52  fof(f125,plain,(
% 1.28/0.52    ~r1_tarski(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)) | (~spl6_2 | spl6_3)),
% 1.28/0.52    inference(backward_demodulation,[],[f111,f124])).
% 1.28/0.52  fof(f124,plain,(
% 1.28/0.52    k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k1_xboole_0) | ~spl6_2),
% 1.28/0.52    inference(backward_demodulation,[],[f116,f122])).
% 1.28/0.52  fof(f116,plain,(
% 1.28/0.52    k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK0)) | ~spl6_2),
% 1.28/0.52    inference(forward_demodulation,[],[f113,f50])).
% 1.28/0.52  fof(f113,plain,(
% 1.28/0.52    k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) | ~spl6_2),
% 1.28/0.52    inference(resolution,[],[f112,f79])).
% 1.28/0.52  fof(f111,plain,(
% 1.28/0.52    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | (~spl6_2 | spl6_3)),
% 1.28/0.52    inference(backward_demodulation,[],[f108,f103])).
% 1.28/0.52  fof(f108,plain,(
% 1.28/0.52    ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | spl6_3),
% 1.28/0.52    inference(avatar_component_clause,[],[f107])).
% 1.28/0.52  fof(f110,plain,(
% 1.28/0.52    spl6_3 | spl6_2),
% 1.28/0.52    inference(avatar_split_clause,[],[f77,f102,f107])).
% 1.28/0.52  fof(f77,plain,(
% 1.28/0.52    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.28/0.52    inference(definition_unfolding,[],[f44,f47])).
% 1.28/0.52  fof(f47,plain,(
% 1.28/0.52    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f11])).
% 1.28/0.52  fof(f11,axiom,(
% 1.28/0.52    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.28/0.52  fof(f44,plain,(
% 1.28/0.52    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.28/0.52    inference(cnf_transformation,[],[f24])).
% 1.28/0.52  fof(f105,plain,(
% 1.28/0.52    ~spl6_1 | ~spl6_2),
% 1.28/0.52    inference(avatar_split_clause,[],[f96,f102,f98])).
% 1.28/0.52  fof(f96,plain,(
% 1.28/0.52    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 1.28/0.52    inference(inner_rewriting,[],[f76])).
% 1.28/0.52  fof(f76,plain,(
% 1.28/0.52    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.28/0.52    inference(definition_unfolding,[],[f45,f47])).
% 1.28/0.52  fof(f45,plain,(
% 1.28/0.52    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.28/0.52    inference(cnf_transformation,[],[f24])).
% 1.28/0.52  % SZS output end Proof for theBenchmark
% 1.28/0.52  % (19491)------------------------------
% 1.28/0.52  % (19491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (19491)Termination reason: Refutation
% 1.28/0.52  
% 1.28/0.52  % (19491)Memory used [KB]: 10874
% 1.28/0.52  % (19491)Time elapsed: 0.123 s
% 1.28/0.52  % (19491)------------------------------
% 1.28/0.52  % (19491)------------------------------
% 1.28/0.52  % (19493)Refutation not found, incomplete strategy% (19493)------------------------------
% 1.28/0.52  % (19493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (19493)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (19493)Memory used [KB]: 10618
% 1.28/0.52  % (19493)Time elapsed: 0.124 s
% 1.28/0.52  % (19493)------------------------------
% 1.28/0.52  % (19493)------------------------------
% 1.28/0.53  % (19482)Success in time 0.173 s
%------------------------------------------------------------------------------
