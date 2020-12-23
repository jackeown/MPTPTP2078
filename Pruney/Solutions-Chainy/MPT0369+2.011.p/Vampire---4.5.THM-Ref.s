%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:25 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 140 expanded)
%              Number of leaves         :   15 (  45 expanded)
%              Depth                    :   18
%              Number of atoms          :  254 ( 591 expanded)
%              Number of equality atoms :   35 (  83 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f343,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f278,f311])).

fof(f311,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f31,f279])).

fof(f279,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(resolution,[],[f67,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f67,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
    & ~ r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(X0)) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(sK0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(sK0)) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,k3_subset_1(sK0,X1))
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(sK0)) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,k3_subset_1(sK0,sK1))
          & ~ r2_hidden(X2,sK1)
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,k3_subset_1(sK0,sK1))
        & ~ r2_hidden(X2,sK1)
        & m1_subset_1(X2,sK0) )
   => ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
      & ~ r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f278,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f70,f266])).

fof(f266,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f243,f61])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f243,plain,(
    ~ r2_hidden(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(global_subsumption,[],[f34,f240])).

fof(f240,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f153,f35])).

fof(f35,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f153,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_subset_1(sK0,sK1))
      | r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,k2_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f135,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f135,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))
      | r2_hidden(X3,k3_subset_1(sK0,sK1)) ) ),
    inference(global_subsumption,[],[f119,f132])).

fof(f132,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK0)
      | r2_hidden(X3,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X3,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK0)
      | r2_hidden(X3,k3_subset_1(sK0,sK1))
      | r2_hidden(X3,sK0)
      | ~ r2_hidden(X3,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ) ),
    inference(resolution,[],[f97,f57])).

fof(f97,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))))
      | r2_hidden(X4,sK0)
      | r2_hidden(X4,k3_subset_1(sK0,sK1)) ) ),
    inference(superposition,[],[f57,f80])).

fof(f80,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f77,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f77,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f32,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f119,plain,(
    ! [X6] :
      ( r2_hidden(X6,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X6,sK0)
      | ~ r2_hidden(X6,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X6] :
      ( r2_hidden(X6,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X6,sK0)
      | ~ r2_hidden(X6,sK0)
      | ~ r2_hidden(X6,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ) ),
    inference(resolution,[],[f96,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f96,plain,(
    ! [X3] :
      ( r2_hidden(X3,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))))
      | r2_hidden(X3,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X3,sK0) ) ),
    inference(superposition,[],[f56,f80])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f34,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f71,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f63,f69,f66])).

fof(f63,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f33,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (25188)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (25180)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (25172)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (25167)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (25169)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (25170)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (25166)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (25165)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.54  % (25190)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.54  % (25171)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.54  % (25167)Refutation found. Thanks to Tanya!
% 1.27/0.54  % SZS status Theorem for theBenchmark
% 1.27/0.54  % SZS output start Proof for theBenchmark
% 1.27/0.54  fof(f343,plain,(
% 1.27/0.54    $false),
% 1.27/0.54    inference(avatar_sat_refutation,[],[f71,f278,f311])).
% 1.27/0.54  fof(f311,plain,(
% 1.27/0.54    ~spl4_1),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f281])).
% 1.27/0.54  fof(f281,plain,(
% 1.27/0.54    $false | ~spl4_1),
% 1.27/0.54    inference(subsumption_resolution,[],[f31,f279])).
% 1.27/0.54  fof(f279,plain,(
% 1.27/0.54    k1_xboole_0 = sK0 | ~spl4_1),
% 1.27/0.54    inference(resolution,[],[f67,f38])).
% 1.27/0.54  fof(f38,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f16])).
% 1.27/0.54  fof(f16,plain,(
% 1.27/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f3])).
% 1.27/0.54  fof(f3,axiom,(
% 1.27/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.27/0.54  fof(f67,plain,(
% 1.27/0.54    v1_xboole_0(sK0) | ~spl4_1),
% 1.27/0.54    inference(avatar_component_clause,[],[f66])).
% 1.27/0.54  fof(f66,plain,(
% 1.27/0.54    spl4_1 <=> v1_xboole_0(sK0)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.27/0.54  fof(f31,plain,(
% 1.27/0.54    k1_xboole_0 != sK0),
% 1.27/0.54    inference(cnf_transformation,[],[f23])).
% 1.27/0.54  fof(f23,plain,(
% 1.27/0.54    ((~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22,f21,f20])).
% 1.27/0.54  fof(f20,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0) => (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0)),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f21,plain,(
% 1.27/0.54    ? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) => (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f22,plain,(
% 1.27/0.54    ? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) => (~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f15,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.27/0.54    inference(flattening,[],[f14])).
% 1.27/0.54  fof(f14,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.27/0.54    inference(ennf_transformation,[],[f13])).
% 1.27/0.54  fof(f13,negated_conjecture,(
% 1.27/0.54    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.27/0.54    inference(negated_conjecture,[],[f12])).
% 1.27/0.54  fof(f12,conjecture,(
% 1.27/0.54    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 1.27/0.54  fof(f278,plain,(
% 1.27/0.54    ~spl4_2),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f277])).
% 1.27/0.54  fof(f277,plain,(
% 1.27/0.54    $false | ~spl4_2),
% 1.27/0.54    inference(subsumption_resolution,[],[f70,f266])).
% 1.27/0.54  fof(f266,plain,(
% 1.27/0.54    ~r2_hidden(sK2,sK0)),
% 1.27/0.54    inference(resolution,[],[f243,f61])).
% 1.27/0.54  fof(f61,plain,(
% 1.27/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 1.27/0.54    inference(equality_resolution,[],[f49])).
% 1.27/0.54  fof(f49,plain,(
% 1.27/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.27/0.54    inference(cnf_transformation,[],[f29])).
% 1.27/0.54  fof(f29,plain,(
% 1.27/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 1.27/0.54  fof(f28,plain,(
% 1.27/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f27,plain,(
% 1.27/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.27/0.54    inference(rectify,[],[f26])).
% 1.27/0.54  fof(f26,plain,(
% 1.27/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.27/0.54    inference(flattening,[],[f25])).
% 1.27/0.54  fof(f25,plain,(
% 1.27/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.27/0.54    inference(nnf_transformation,[],[f2])).
% 1.27/0.54  fof(f2,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.27/0.54  fof(f243,plain,(
% 1.27/0.54    ~r2_hidden(sK2,k2_xboole_0(sK0,sK1))),
% 1.27/0.54    inference(global_subsumption,[],[f34,f240])).
% 1.27/0.54  fof(f240,plain,(
% 1.27/0.54    r2_hidden(sK2,sK1) | ~r2_hidden(sK2,k2_xboole_0(sK0,sK1))),
% 1.27/0.54    inference(resolution,[],[f153,f35])).
% 1.27/0.54  fof(f35,plain,(
% 1.27/0.54    ~r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 1.27/0.54    inference(cnf_transformation,[],[f23])).
% 1.27/0.54  fof(f153,plain,(
% 1.27/0.54    ( ! [X2] : (r2_hidden(X2,k3_subset_1(sK0,sK1)) | r2_hidden(X2,sK1) | ~r2_hidden(X2,k2_xboole_0(sK0,sK1))) )),
% 1.27/0.54    inference(resolution,[],[f135,f57])).
% 1.27/0.54  fof(f57,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f30])).
% 1.27/0.54  fof(f30,plain,(
% 1.27/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.27/0.54    inference(nnf_transformation,[],[f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.27/0.54    inference(ennf_transformation,[],[f4])).
% 1.27/0.54  fof(f4,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.27/0.54  fof(f135,plain,(
% 1.27/0.54    ( ! [X3] : (~r2_hidden(X3,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))) | r2_hidden(X3,k3_subset_1(sK0,sK1))) )),
% 1.27/0.54    inference(global_subsumption,[],[f119,f132])).
% 1.27/0.54  fof(f132,plain,(
% 1.27/0.54    ( ! [X3] : (r2_hidden(X3,sK0) | r2_hidden(X3,k3_subset_1(sK0,sK1)) | ~r2_hidden(X3,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) )),
% 1.27/0.54    inference(duplicate_literal_removal,[],[f128])).
% 1.27/0.54  fof(f128,plain,(
% 1.27/0.54    ( ! [X3] : (r2_hidden(X3,sK0) | r2_hidden(X3,k3_subset_1(sK0,sK1)) | r2_hidden(X3,sK0) | ~r2_hidden(X3,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) )),
% 1.27/0.54    inference(resolution,[],[f97,f57])).
% 1.27/0.54  fof(f97,plain,(
% 1.27/0.54    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) | r2_hidden(X4,sK0) | r2_hidden(X4,k3_subset_1(sK0,sK1))) )),
% 1.27/0.54    inference(superposition,[],[f57,f80])).
% 1.27/0.54  fof(f80,plain,(
% 1.27/0.54    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))))),
% 1.27/0.54    inference(forward_demodulation,[],[f77,f47])).
% 1.27/0.54  fof(f47,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f7])).
% 1.27/0.54  fof(f7,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.27/0.54  fof(f77,plain,(
% 1.27/0.54    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)))),
% 1.27/0.54    inference(resolution,[],[f32,f59])).
% 1.27/0.54  fof(f59,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.27/0.54    inference(definition_unfolding,[],[f46,f58])).
% 1.27/0.54  fof(f58,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.27/0.54    inference(definition_unfolding,[],[f40,f41])).
% 1.27/0.54  fof(f41,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f9])).
% 1.27/0.54  fof(f9,axiom,(
% 1.27/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.27/0.54  fof(f40,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f5])).
% 1.27/0.54  fof(f5,axiom,(
% 1.27/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.27/0.54  fof(f46,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f18])).
% 1.27/0.54  fof(f18,plain,(
% 1.27/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.27/0.54    inference(ennf_transformation,[],[f11])).
% 1.27/0.54  fof(f11,axiom,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.27/0.54  fof(f32,plain,(
% 1.27/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.27/0.54    inference(cnf_transformation,[],[f23])).
% 1.27/0.54  fof(f119,plain,(
% 1.27/0.54    ( ! [X6] : (r2_hidden(X6,k3_subset_1(sK0,sK1)) | ~r2_hidden(X6,sK0) | ~r2_hidden(X6,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) )),
% 1.27/0.54    inference(duplicate_literal_removal,[],[f118])).
% 1.27/0.54  fof(f118,plain,(
% 1.27/0.54    ( ! [X6] : (r2_hidden(X6,k3_subset_1(sK0,sK1)) | ~r2_hidden(X6,sK0) | ~r2_hidden(X6,sK0) | ~r2_hidden(X6,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) )),
% 1.27/0.54    inference(resolution,[],[f96,f55])).
% 1.27/0.54  fof(f55,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f30])).
% 1.27/0.54  fof(f96,plain,(
% 1.27/0.54    ( ! [X3] : (r2_hidden(X3,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) | r2_hidden(X3,k3_subset_1(sK0,sK1)) | ~r2_hidden(X3,sK0)) )),
% 1.27/0.54    inference(superposition,[],[f56,f80])).
% 1.27/0.54  fof(f56,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f30])).
% 1.27/0.54  fof(f34,plain,(
% 1.27/0.54    ~r2_hidden(sK2,sK1)),
% 1.27/0.54    inference(cnf_transformation,[],[f23])).
% 1.27/0.54  fof(f70,plain,(
% 1.27/0.54    r2_hidden(sK2,sK0) | ~spl4_2),
% 1.27/0.54    inference(avatar_component_clause,[],[f69])).
% 1.27/0.54  fof(f69,plain,(
% 1.27/0.54    spl4_2 <=> r2_hidden(sK2,sK0)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.27/0.54  fof(f71,plain,(
% 1.27/0.54    spl4_1 | spl4_2),
% 1.27/0.54    inference(avatar_split_clause,[],[f63,f69,f66])).
% 1.27/0.54  fof(f63,plain,(
% 1.27/0.54    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 1.27/0.54    inference(resolution,[],[f33,f42])).
% 1.27/0.54  fof(f42,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f24])).
% 1.27/0.54  fof(f24,plain,(
% 1.27/0.54    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.27/0.54    inference(nnf_transformation,[],[f17])).
% 1.27/0.54  fof(f17,plain,(
% 1.27/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.27/0.54    inference(ennf_transformation,[],[f10])).
% 1.27/0.54  fof(f10,axiom,(
% 1.27/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.27/0.54  fof(f33,plain,(
% 1.27/0.54    m1_subset_1(sK2,sK0)),
% 1.27/0.54    inference(cnf_transformation,[],[f23])).
% 1.27/0.54  % SZS output end Proof for theBenchmark
% 1.27/0.54  % (25167)------------------------------
% 1.27/0.54  % (25167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (25167)Termination reason: Refutation
% 1.27/0.54  
% 1.27/0.54  % (25167)Memory used [KB]: 11001
% 1.27/0.54  % (25167)Time elapsed: 0.140 s
% 1.27/0.54  % (25167)------------------------------
% 1.27/0.54  % (25167)------------------------------
% 1.27/0.54  % (25191)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.54  % (25192)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.27/0.54  % (25193)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.54  % (25189)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.54  % (25183)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.54  % (25185)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.54  % (25184)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.27/0.54  % (25175)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.54  % (25181)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.54  % (25178)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.54  % (25177)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.55  % (25186)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.55  % (25182)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.55  % (25174)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.55  % (25194)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.55  % (25182)Refutation not found, incomplete strategy% (25182)------------------------------
% 1.50/0.55  % (25182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (25173)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.56  % (25179)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.56  % (25182)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (25182)Memory used [KB]: 10618
% 1.50/0.56  % (25182)Time elapsed: 0.151 s
% 1.50/0.56  % (25182)------------------------------
% 1.50/0.56  % (25182)------------------------------
% 1.50/0.57  % (25164)Success in time 0.204 s
%------------------------------------------------------------------------------
