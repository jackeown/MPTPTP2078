%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 844 expanded)
%              Number of leaves         :   20 ( 213 expanded)
%              Depth                    :   21
%              Number of atoms          :  436 (3919 expanded)
%              Number of equality atoms :   86 ( 794 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f228,f230,f306])).

fof(f306,plain,
    ( spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f298,f103])).

fof(f103,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f298,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_3 ),
    inference(resolution,[],[f296,f48])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f296,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f295,f90])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f295,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k4_xboole_0(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f287,f276])).

fof(f276,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f271,f256])).

fof(f256,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f91,f239])).

fof(f239,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f237,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f237,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f236,f88])).

fof(f88,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f236,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f233,f46])).

fof(f46,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f233,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f271,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f90,f242])).

fof(f242,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f241,f239])).

fof(f241,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f237,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f56,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f287,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,k4_xboole_0(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_3 ),
    inference(superposition,[],[f89,f243])).

fof(f243,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f235,f63])).

fof(f235,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f108,f232])).

fof(f232,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f43,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f108,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_3
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f230,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f99,f217])).

fof(f217,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_2 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl6_2 ),
    inference(superposition,[],[f62,f180])).

fof(f180,plain,
    ( ! [X16] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X16)
    | ~ spl6_2 ),
    inference(resolution,[],[f136,f134])).

fof(f134,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_xboole_0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f133,f126])).

fof(f126,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl6_2 ),
    inference(superposition,[],[f90,f119])).

fof(f119,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f117,f63])).

fof(f117,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f116,f88])).

fof(f116,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f113,f46])).

fof(f113,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f111,f52])).

fof(f111,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f43,f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f133,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | r2_hidden(X4,sK0) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f129,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f121,f119])).

fof(f121,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f117,f80])).

fof(f129,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k4_xboole_0(k1_xboole_0,k1_xboole_0))
        | r2_hidden(X4,sK0) )
    | ~ spl6_2 ),
    inference(superposition,[],[f93,f119])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f71,f51])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f136,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,k1_xboole_0),X0)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl6_2 ),
    inference(resolution,[],[f134,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f99,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_1
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f228,plain,
    ( ~ spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl6_2
    | spl6_3 ),
    inference(resolution,[],[f217,f115])).

fof(f115,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl6_2
    | spl6_3 ),
    inference(backward_demodulation,[],[f110,f112])).

fof(f112,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(resolution,[],[f111,f57])).

fof(f110,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | ~ spl6_2
    | spl6_3 ),
    inference(backward_demodulation,[],[f107,f102])).

fof(f107,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f109,plain,
    ( spl6_3
    | spl6_2 ),
    inference(avatar_split_clause,[],[f78,f101,f106])).

fof(f78,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f44,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f95,f101,f97])).

fof(f95,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f77])).

fof(f77,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (19205)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (19197)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (19194)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (19197)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (19202)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (19210)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (19218)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f307,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f104,f109,f228,f230,f306])).
% 0.21/0.55  fof(f306,plain,(
% 0.21/0.55    spl6_2 | ~spl6_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f305])).
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    $false | (spl6_2 | ~spl6_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f298,f103])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | spl6_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f101])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    spl6_2 <=> k1_xboole_0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.55  fof(f298,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | ~spl6_3),
% 0.21/0.55    inference(resolution,[],[f296,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.55  fof(f296,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f295,f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(rectify,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(flattening,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.55  fof(f295,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,k4_xboole_0(sK0,sK1)) | ~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f287,f276])).
% 0.21/0.55  fof(f276,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f271,f256])).
% 0.21/0.55  fof(f256,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,sK1)) )),
% 0.21/0.55    inference(superposition,[],[f91,f239])).
% 0.21/0.55  fof(f239,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.21/0.55    inference(resolution,[],[f237,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(nnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.55  fof(f237,plain,(
% 0.21/0.55    r1_tarski(sK1,sK0)),
% 0.21/0.55    inference(resolution,[],[f236,f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(rectify,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(subsumption_resolution,[],[f233,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.55  fof(f233,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(resolution,[],[f43,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.55    inference(negated_conjecture,[],[f14])).
% 0.21/0.55  fof(f14,conjecture,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f271,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.55    inference(superposition,[],[f90,f242])).
% 0.21/0.55  fof(f242,plain,(
% 0.21/0.55    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f241,f239])).
% 0.21/0.55  fof(f241,plain,(
% 0.21/0.55    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 0.21/0.55    inference(resolution,[],[f237,f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f56,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f287,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,k4_xboole_0(sK0,sK1)) | ~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 0.21/0.55    inference(superposition,[],[f89,f243])).
% 0.21/0.55  fof(f243,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~spl6_3),
% 0.21/0.55    inference(resolution,[],[f235,f63])).
% 0.21/0.55  fof(f235,plain,(
% 0.21/0.55    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | ~spl6_3),
% 0.21/0.55    inference(backward_demodulation,[],[f108,f232])).
% 0.21/0.55  fof(f232,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.55    inference(resolution,[],[f43,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl6_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f106])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    spl6_3 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    spl6_1 | ~spl6_2),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.55  fof(f229,plain,(
% 0.21/0.55    $false | (spl6_1 | ~spl6_2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f99,f217])).
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl6_2),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f201])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) ) | ~spl6_2),
% 0.21/0.55    inference(superposition,[],[f62,f180])).
% 0.21/0.55  fof(f180,plain,(
% 0.21/0.55    ( ! [X16] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X16)) ) | ~spl6_2),
% 0.21/0.55    inference(resolution,[],[f136,f134])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) ) | ~spl6_2),
% 0.21/0.55    inference(subsumption_resolution,[],[f133,f126])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_2),
% 0.21/0.55    inference(superposition,[],[f90,f119])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) | ~spl6_2),
% 0.21/0.55    inference(resolution,[],[f117,f63])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    r1_tarski(k1_xboole_0,sK0) | ~spl6_2),
% 0.21/0.55    inference(resolution,[],[f116,f88])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl6_2),
% 0.21/0.55    inference(subsumption_resolution,[],[f113,f46])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl6_2),
% 0.21/0.55    inference(resolution,[],[f111,f52])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl6_2),
% 0.21/0.55    inference(backward_demodulation,[],[f43,f102])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | ~spl6_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f101])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | r2_hidden(X4,sK0)) ) | ~spl6_2),
% 0.21/0.55    inference(forward_demodulation,[],[f129,f122])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl6_2),
% 0.21/0.55    inference(forward_demodulation,[],[f121,f119])).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)) | ~spl6_2),
% 0.21/0.55    inference(resolution,[],[f117,f80])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | r2_hidden(X4,sK0)) ) | ~spl6_2),
% 0.21/0.55    inference(superposition,[],[f93,f119])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X4,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 0.21/0.55    inference(definition_unfolding,[],[f71,f51])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(rectify,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(flattening,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,k1_xboole_0),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl6_2),
% 0.21/0.55    inference(resolution,[],[f134,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | spl6_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f97])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    spl6_1 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.55  fof(f228,plain,(
% 0.21/0.55    ~spl6_2 | spl6_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f224])).
% 0.21/0.55  fof(f224,plain,(
% 0.21/0.55    $false | (~spl6_2 | spl6_3)),
% 0.21/0.55    inference(resolution,[],[f217,f115])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) | (~spl6_2 | spl6_3)),
% 0.21/0.55    inference(backward_demodulation,[],[f110,f112])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    k3_subset_1(sK0,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0) | ~spl6_2),
% 0.21/0.55    inference(resolution,[],[f111,f57])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | (~spl6_2 | spl6_3)),
% 0.21/0.55    inference(backward_demodulation,[],[f107,f102])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | spl6_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f106])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    spl6_3 | spl6_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f78,f101,f106])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    inference(definition_unfolding,[],[f44,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ~spl6_1 | ~spl6_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f95,f101,f97])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.21/0.55    inference(inner_rewriting,[],[f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    inference(definition_unfolding,[],[f45,f47])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (19197)------------------------------
% 0.21/0.55  % (19197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19197)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (19197)Memory used [KB]: 10746
% 0.21/0.55  % (19197)Time elapsed: 0.086 s
% 0.21/0.55  % (19197)------------------------------
% 0.21/0.55  % (19197)------------------------------
% 0.21/0.55  % (19185)Success in time 0.181 s
%------------------------------------------------------------------------------
