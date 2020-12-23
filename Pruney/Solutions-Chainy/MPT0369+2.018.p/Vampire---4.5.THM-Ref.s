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
% DateTime   : Thu Dec  3 12:45:25 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 431 expanded)
%              Number of leaves         :   24 ( 140 expanded)
%              Depth                    :   20
%              Number of atoms          :  410 (1979 expanded)
%              Number of equality atoms :   50 ( 282 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f560,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f143,f224,f233,f246,f247,f270,f271,f287,f426,f540,f559])).

fof(f559,plain,
    ( ~ spl6_10
    | ~ spl6_13
    | ~ spl6_23
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_23
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f33,f505])).

fof(f505,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_23
    | ~ spl6_30 ),
    inference(resolution,[],[f457,f223])).

fof(f223,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl6_23
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f457,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(k1_xboole_0,X0,X1),X1)
        | sK0 = X1 )
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f438,f439])).

fof(f439,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(k1_xboole_0,X0,X1),sK0)
        | r2_hidden(sK5(k1_xboole_0,X0,X1),X1)
        | sK0 = X1 )
    | ~ spl6_10
    | ~ spl6_30 ),
    inference(backward_demodulation,[],[f321,f425])).

fof(f425,plain,
    ( ! [X1] : sK0 = k3_xboole_0(k1_xboole_0,X1)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl6_30
  <=> ! [X1] : sK0 = k3_xboole_0(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f321,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(k1_xboole_0,X0,X1),sK0)
        | r2_hidden(sK5(k1_xboole_0,X0,X1),X1)
        | k3_xboole_0(k1_xboole_0,X0) = X1 )
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f320,f121])).

fof(f121,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_10
  <=> k1_xboole_0 = k3_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f320,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(k1_xboole_0,X0,X1),X1)
        | r2_hidden(sK5(k1_xboole_0,X0,X1),sK0)
        | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1 )
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f319,f121])).

fof(f319,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(k1_xboole_0,X0,X1),sK0)
        | r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1)
        | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1 )
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f242,f121])).

fof(f242,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),sK0)
      | r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1)
      | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1 ) ),
    inference(resolution,[],[f234,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

% (1891)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f30,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f234,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK0,sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(global_subsumption,[],[f100])).

% (1888)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK0,sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k3_subset_1(sK0,sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f92,f60])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_xboole_0(sK0,sK1))
      | r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k3_subset_1(sK0,sK1)) ) ),
    inference(superposition,[],[f53,f75])).

fof(f75,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f34,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
    & ~ r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
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

fof(f18,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,k3_subset_1(sK0,sK1))
        & ~ r2_hidden(X2,sK1)
        & m1_subset_1(X2,sK0) )
   => ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
      & ~ r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f438,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(k1_xboole_0,X0,X1),X1)
        | sK0 = X1
        | ~ r2_hidden(sK5(k1_xboole_0,X0,X1),sK0) )
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_30 ),
    inference(backward_demodulation,[],[f399,f425])).

fof(f399,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(k1_xboole_0,X0,X1),X1)
        | k3_xboole_0(k1_xboole_0,X0) = X1
        | ~ r2_hidden(sK5(k1_xboole_0,X0,X1),sK0) )
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f398,f121])).

fof(f398,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(k1_xboole_0,X0,X1),X1)
        | ~ r2_hidden(sK5(k1_xboole_0,X0,X1),sK0)
        | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1 )
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f397,f121])).

fof(f397,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(k1_xboole_0,X0,X1),sK0)
        | r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1)
        | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1 )
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f291,f121])).

fof(f291,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),sK0)
        | r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1)
        | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1 )
    | ~ spl6_13 ),
    inference(resolution,[],[f279,f50])).

fof(f279,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_subset_1(sK0,sK1))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f93,f137])).

fof(f137,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k3_xboole_0(sK0,sK1))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_13
  <=> ! [X1] :
        ( r2_hidden(X1,k3_xboole_0(sK0,sK1))
        | ~ r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f93,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,k3_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f54,f75])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f540,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f538,f67,f64])).

fof(f64,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f67,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f538,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f35,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f35,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f426,plain,
    ( ~ spl6_1
    | spl6_30
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f421,f120,f424,f64])).

fof(f421,plain,
    ( ! [X1] :
        ( sK0 = k3_xboole_0(k1_xboole_0,X1)
        | ~ v1_xboole_0(sK0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f331,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f331,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_xboole_0,X0,sK0),sK0)
        | sK0 = k3_xboole_0(k1_xboole_0,X0) )
    | ~ spl6_10 ),
    inference(factoring,[],[f321])).

fof(f287,plain,
    ( ~ spl6_1
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f65,f273])).

fof(f273,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f153,f38])).

fof(f153,plain,
    ( r2_hidden(sK4(k3_subset_1(sK0,sK1)),sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_12
  <=> r2_hidden(sK4(k3_subset_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f65,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f271,plain,
    ( ~ spl6_7
    | spl6_13 ),
    inference(avatar_split_clause,[],[f264,f136,f110])).

fof(f110,plain,
    ( spl6_7
  <=> v1_xboole_0(k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f264,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_xboole_0(sK0,sK1))
      | ~ r2_hidden(X2,sK0)
      | ~ v1_xboole_0(k3_subset_1(sK0,sK1)) ) ),
    inference(resolution,[],[f94,f38])).

fof(f94,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_subset_1(sK0,sK1))
      | r2_hidden(X2,k3_xboole_0(sK0,sK1))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f55,f75])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f270,plain,
    ( ~ spl6_1
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f65,f268])).

fof(f268,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f151,f38])).

fof(f151,plain,
    ( r2_hidden(sK3(k3_subset_1(sK0,sK1)),sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_9
  <=> r2_hidden(sK3(k3_subset_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f247,plain,
    ( spl6_10
    | spl6_12 ),
    inference(avatar_split_clause,[],[f241,f126,f120])).

fof(f241,plain,
    ( r2_hidden(sK4(k3_subset_1(sK0,sK1)),sK0)
    | k1_xboole_0 = k3_subset_1(sK0,sK1) ),
    inference(resolution,[],[f234,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f246,plain,
    ( spl6_7
    | spl6_9 ),
    inference(avatar_split_clause,[],[f240,f116,f110])).

fof(f240,plain,
    ( r2_hidden(sK3(k3_subset_1(sK0,sK1)),sK0)
    | v1_xboole_0(k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f234,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f233,plain,(
    ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f36,f229])).

fof(f229,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_14 ),
    inference(resolution,[],[f142,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f142,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_14
  <=> r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f36,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f224,plain,
    ( ~ spl6_1
    | spl6_23
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f217,f120,f222,f64])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ v1_xboole_0(sK0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f160,f38])).

fof(f160,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f100,f121])).

fof(f143,plain,
    ( ~ spl6_2
    | spl6_14 ),
    inference(avatar_split_clause,[],[f132,f141,f67])).

fof(f132,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f94,f37])).

fof(f37,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (1889)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.55  % (1904)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.55  % (1912)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.55  % (1895)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.56  % (1914)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.56  % (1901)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.56  % (1887)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.56  % (1889)Refutation found. Thanks to Tanya!
% 1.29/0.56  % SZS status Theorem for theBenchmark
% 1.29/0.57  % (1897)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.59/0.57  % (1897)Refutation not found, incomplete strategy% (1897)------------------------------
% 1.59/0.57  % (1897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (1892)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.59/0.57  % (1897)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (1897)Memory used [KB]: 10618
% 1.59/0.57  % (1897)Time elapsed: 0.142 s
% 1.59/0.57  % (1897)------------------------------
% 1.59/0.57  % (1897)------------------------------
% 1.59/0.57  % (1890)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.59/0.57  % SZS output start Proof for theBenchmark
% 1.59/0.57  fof(f560,plain,(
% 1.59/0.57    $false),
% 1.59/0.57    inference(avatar_sat_refutation,[],[f143,f224,f233,f246,f247,f270,f271,f287,f426,f540,f559])).
% 1.59/0.57  fof(f559,plain,(
% 1.59/0.57    ~spl6_10 | ~spl6_13 | ~spl6_23 | ~spl6_30),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f551])).
% 1.59/0.57  fof(f551,plain,(
% 1.59/0.57    $false | (~spl6_10 | ~spl6_13 | ~spl6_23 | ~spl6_30)),
% 1.59/0.57    inference(subsumption_resolution,[],[f33,f505])).
% 1.59/0.57  fof(f505,plain,(
% 1.59/0.57    k1_xboole_0 = sK0 | (~spl6_10 | ~spl6_13 | ~spl6_23 | ~spl6_30)),
% 1.59/0.57    inference(resolution,[],[f457,f223])).
% 1.59/0.57  fof(f223,plain,(
% 1.59/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_23),
% 1.59/0.57    inference(avatar_component_clause,[],[f222])).
% 1.59/0.57  fof(f222,plain,(
% 1.59/0.57    spl6_23 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.59/0.57  fof(f457,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(sK5(k1_xboole_0,X0,X1),X1) | sK0 = X1) ) | (~spl6_10 | ~spl6_13 | ~spl6_30)),
% 1.59/0.57    inference(subsumption_resolution,[],[f438,f439])).
% 1.59/0.57  fof(f439,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(sK5(k1_xboole_0,X0,X1),sK0) | r2_hidden(sK5(k1_xboole_0,X0,X1),X1) | sK0 = X1) ) | (~spl6_10 | ~spl6_30)),
% 1.59/0.57    inference(backward_demodulation,[],[f321,f425])).
% 1.59/0.57  fof(f425,plain,(
% 1.59/0.57    ( ! [X1] : (sK0 = k3_xboole_0(k1_xboole_0,X1)) ) | ~spl6_30),
% 1.59/0.57    inference(avatar_component_clause,[],[f424])).
% 1.59/0.57  fof(f424,plain,(
% 1.59/0.57    spl6_30 <=> ! [X1] : sK0 = k3_xboole_0(k1_xboole_0,X1)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.59/0.57  fof(f321,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(sK5(k1_xboole_0,X0,X1),sK0) | r2_hidden(sK5(k1_xboole_0,X0,X1),X1) | k3_xboole_0(k1_xboole_0,X0) = X1) ) | ~spl6_10),
% 1.59/0.57    inference(forward_demodulation,[],[f320,f121])).
% 1.59/0.57  fof(f121,plain,(
% 1.59/0.57    k1_xboole_0 = k3_subset_1(sK0,sK1) | ~spl6_10),
% 1.59/0.57    inference(avatar_component_clause,[],[f120])).
% 1.59/0.57  fof(f120,plain,(
% 1.59/0.57    spl6_10 <=> k1_xboole_0 = k3_subset_1(sK0,sK1)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.59/0.57  fof(f320,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(sK5(k1_xboole_0,X0,X1),X1) | r2_hidden(sK5(k1_xboole_0,X0,X1),sK0) | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1) ) | ~spl6_10),
% 1.59/0.57    inference(forward_demodulation,[],[f319,f121])).
% 1.59/0.57  fof(f319,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(sK5(k1_xboole_0,X0,X1),sK0) | r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1) | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1) ) | ~spl6_10),
% 1.59/0.57    inference(forward_demodulation,[],[f242,f121])).
% 1.59/0.57  fof(f242,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),sK0) | r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1) | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1) )),
% 1.59/0.57    inference(resolution,[],[f234,f50])).
% 1.59/0.57  fof(f50,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 1.59/0.57    inference(cnf_transformation,[],[f31])).
% 1.59/0.57  fof(f31,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.59/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 1.59/0.57  % (1891)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.59/0.57  fof(f30,plain,(
% 1.59/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.59/0.57    introduced(choice_axiom,[])).
% 1.59/0.57  fof(f29,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.59/0.57    inference(rectify,[],[f28])).
% 1.59/0.57  fof(f28,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.59/0.57    inference(flattening,[],[f27])).
% 1.59/0.57  fof(f27,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.59/0.57    inference(nnf_transformation,[],[f2])).
% 1.59/0.57  fof(f2,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.59/0.57  fof(f234,plain,(
% 1.59/0.57    ( ! [X0] : (~r2_hidden(X0,k3_subset_1(sK0,sK1)) | r2_hidden(X0,sK0)) )),
% 1.59/0.57    inference(global_subsumption,[],[f100])).
% 1.59/0.57  % (1888)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.59/0.57  fof(f100,plain,(
% 1.59/0.57    ( ! [X0] : (~r2_hidden(X0,k3_subset_1(sK0,sK1)) | r2_hidden(X0,sK0)) )),
% 1.59/0.57    inference(duplicate_literal_removal,[],[f96])).
% 1.59/0.57  fof(f96,plain,(
% 1.59/0.57    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,k3_subset_1(sK0,sK1)) | r2_hidden(X0,sK0)) )),
% 1.59/0.57    inference(resolution,[],[f92,f60])).
% 1.59/0.57  fof(f60,plain,(
% 1.59/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.59/0.57    inference(equality_resolution,[],[f47])).
% 1.59/0.57  fof(f47,plain,(
% 1.59/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.59/0.57    inference(cnf_transformation,[],[f31])).
% 1.59/0.57  fof(f92,plain,(
% 1.59/0.57    ( ! [X0] : (r2_hidden(X0,k3_xboole_0(sK0,sK1)) | r2_hidden(X0,sK0) | ~r2_hidden(X0,k3_subset_1(sK0,sK1))) )),
% 1.59/0.57    inference(superposition,[],[f53,f75])).
% 1.59/0.57  fof(f75,plain,(
% 1.59/0.57    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.59/0.57    inference(resolution,[],[f34,f57])).
% 1.59/0.57  fof(f57,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.59/0.57    inference(definition_unfolding,[],[f46,f41])).
% 1.59/0.57  fof(f41,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f5])).
% 1.59/0.57  fof(f5,axiom,(
% 1.59/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.59/0.57  fof(f46,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f14])).
% 1.59/0.57  fof(f14,plain,(
% 1.59/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f7])).
% 1.59/0.57  fof(f7,axiom,(
% 1.59/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.59/0.57  fof(f34,plain,(
% 1.59/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.59/0.57    inference(cnf_transformation,[],[f19])).
% 1.59/0.57  fof(f19,plain,(
% 1.59/0.57    ((~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0),
% 1.59/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17,f16])).
% 1.59/0.57  fof(f16,plain,(
% 1.59/0.57    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0) => (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0)),
% 1.59/0.57    introduced(choice_axiom,[])).
% 1.59/0.57  fof(f17,plain,(
% 1.59/0.57    ? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) => (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.59/0.57    introduced(choice_axiom,[])).
% 1.59/0.57  fof(f18,plain,(
% 1.59/0.57    ? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) => (~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0))),
% 1.59/0.57    introduced(choice_axiom,[])).
% 1.59/0.57  fof(f11,plain,(
% 1.59/0.57    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.59/0.57    inference(flattening,[],[f10])).
% 1.59/0.57  fof(f10,plain,(
% 1.59/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.59/0.57    inference(ennf_transformation,[],[f9])).
% 1.59/0.57  fof(f9,negated_conjecture,(
% 1.59/0.57    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.59/0.57    inference(negated_conjecture,[],[f8])).
% 1.59/0.57  fof(f8,conjecture,(
% 1.59/0.57    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 1.59/0.57  fof(f53,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f32])).
% 1.59/0.57  fof(f32,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.59/0.57    inference(nnf_transformation,[],[f15])).
% 1.59/0.57  fof(f15,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.59/0.57    inference(ennf_transformation,[],[f3])).
% 1.59/0.57  fof(f3,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.59/0.57  fof(f438,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(sK5(k1_xboole_0,X0,X1),X1) | sK0 = X1 | ~r2_hidden(sK5(k1_xboole_0,X0,X1),sK0)) ) | (~spl6_10 | ~spl6_13 | ~spl6_30)),
% 1.59/0.57    inference(backward_demodulation,[],[f399,f425])).
% 1.59/0.57  fof(f399,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(sK5(k1_xboole_0,X0,X1),X1) | k3_xboole_0(k1_xboole_0,X0) = X1 | ~r2_hidden(sK5(k1_xboole_0,X0,X1),sK0)) ) | (~spl6_10 | ~spl6_13)),
% 1.59/0.57    inference(forward_demodulation,[],[f398,f121])).
% 1.59/0.57  fof(f398,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(sK5(k1_xboole_0,X0,X1),X1) | ~r2_hidden(sK5(k1_xboole_0,X0,X1),sK0) | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1) ) | (~spl6_10 | ~spl6_13)),
% 1.59/0.57    inference(forward_demodulation,[],[f397,f121])).
% 1.59/0.57  fof(f397,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(k1_xboole_0,X0,X1),sK0) | r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1) | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1) ) | (~spl6_10 | ~spl6_13)),
% 1.59/0.57    inference(forward_demodulation,[],[f291,f121])).
% 1.59/0.57  fof(f291,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),sK0) | r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1) | k3_xboole_0(k3_subset_1(sK0,sK1),X0) = X1) ) | ~spl6_13),
% 1.59/0.57    inference(resolution,[],[f279,f50])).
% 1.59/0.57  fof(f279,plain,(
% 1.59/0.57    ( ! [X1] : (~r2_hidden(X1,k3_subset_1(sK0,sK1)) | ~r2_hidden(X1,sK0)) ) | ~spl6_13),
% 1.59/0.57    inference(subsumption_resolution,[],[f93,f137])).
% 1.59/0.57  fof(f137,plain,(
% 1.59/0.57    ( ! [X1] : (r2_hidden(X1,k3_xboole_0(sK0,sK1)) | ~r2_hidden(X1,sK0)) ) | ~spl6_13),
% 1.59/0.57    inference(avatar_component_clause,[],[f136])).
% 1.59/0.57  fof(f136,plain,(
% 1.59/0.57    spl6_13 <=> ! [X1] : (r2_hidden(X1,k3_xboole_0(sK0,sK1)) | ~r2_hidden(X1,sK0))),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.59/0.57  fof(f93,plain,(
% 1.59/0.57    ( ! [X1] : (~r2_hidden(X1,k3_subset_1(sK0,sK1)) | ~r2_hidden(X1,sK0) | ~r2_hidden(X1,k3_xboole_0(sK0,sK1))) )),
% 1.59/0.57    inference(superposition,[],[f54,f75])).
% 1.59/0.57  fof(f54,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f32])).
% 1.59/0.57  fof(f33,plain,(
% 1.59/0.57    k1_xboole_0 != sK0),
% 1.59/0.57    inference(cnf_transformation,[],[f19])).
% 1.59/0.57  fof(f540,plain,(
% 1.59/0.57    spl6_1 | spl6_2),
% 1.59/0.57    inference(avatar_split_clause,[],[f538,f67,f64])).
% 1.59/0.57  fof(f64,plain,(
% 1.59/0.57    spl6_1 <=> v1_xboole_0(sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.59/0.57  fof(f67,plain,(
% 1.59/0.57    spl6_2 <=> r2_hidden(sK2,sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.59/0.57  fof(f538,plain,(
% 1.59/0.57    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 1.59/0.57    inference(resolution,[],[f35,f42])).
% 1.59/0.57  fof(f42,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f26])).
% 1.59/0.57  fof(f26,plain,(
% 1.59/0.57    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.59/0.57    inference(nnf_transformation,[],[f13])).
% 1.59/0.57  fof(f13,plain,(
% 1.59/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f6])).
% 1.59/0.57  fof(f6,axiom,(
% 1.59/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.59/0.57  fof(f35,plain,(
% 1.59/0.57    m1_subset_1(sK2,sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f19])).
% 1.59/0.57  fof(f426,plain,(
% 1.59/0.57    ~spl6_1 | spl6_30 | ~spl6_10),
% 1.59/0.57    inference(avatar_split_clause,[],[f421,f120,f424,f64])).
% 1.59/0.57  fof(f421,plain,(
% 1.59/0.57    ( ! [X1] : (sK0 = k3_xboole_0(k1_xboole_0,X1) | ~v1_xboole_0(sK0)) ) | ~spl6_10),
% 1.59/0.57    inference(resolution,[],[f331,f38])).
% 1.59/0.57  fof(f38,plain,(
% 1.59/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f23])).
% 1.59/0.57  fof(f23,plain,(
% 1.59/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.59/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 1.59/0.57  fof(f22,plain,(
% 1.59/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.59/0.57    introduced(choice_axiom,[])).
% 1.59/0.57  fof(f21,plain,(
% 1.59/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.59/0.57    inference(rectify,[],[f20])).
% 1.59/0.57  fof(f20,plain,(
% 1.59/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.59/0.57    inference(nnf_transformation,[],[f1])).
% 1.59/0.57  fof(f1,axiom,(
% 1.59/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.59/0.57  fof(f331,plain,(
% 1.59/0.57    ( ! [X0] : (r2_hidden(sK5(k1_xboole_0,X0,sK0),sK0) | sK0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl6_10),
% 1.59/0.57    inference(factoring,[],[f321])).
% 1.59/0.57  fof(f287,plain,(
% 1.59/0.57    ~spl6_1 | ~spl6_12),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f286])).
% 1.59/0.57  fof(f286,plain,(
% 1.59/0.57    $false | (~spl6_1 | ~spl6_12)),
% 1.59/0.57    inference(subsumption_resolution,[],[f65,f273])).
% 1.59/0.57  fof(f273,plain,(
% 1.59/0.57    ~v1_xboole_0(sK0) | ~spl6_12),
% 1.59/0.57    inference(resolution,[],[f153,f38])).
% 1.59/0.57  fof(f153,plain,(
% 1.59/0.57    r2_hidden(sK4(k3_subset_1(sK0,sK1)),sK0) | ~spl6_12),
% 1.59/0.57    inference(avatar_component_clause,[],[f126])).
% 1.59/0.58  fof(f126,plain,(
% 1.59/0.58    spl6_12 <=> r2_hidden(sK4(k3_subset_1(sK0,sK1)),sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.59/0.58  fof(f65,plain,(
% 1.59/0.58    v1_xboole_0(sK0) | ~spl6_1),
% 1.59/0.58    inference(avatar_component_clause,[],[f64])).
% 1.59/0.58  fof(f271,plain,(
% 1.59/0.58    ~spl6_7 | spl6_13),
% 1.59/0.58    inference(avatar_split_clause,[],[f264,f136,f110])).
% 1.59/0.58  fof(f110,plain,(
% 1.59/0.58    spl6_7 <=> v1_xboole_0(k3_subset_1(sK0,sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.59/0.58  fof(f264,plain,(
% 1.59/0.58    ( ! [X2] : (r2_hidden(X2,k3_xboole_0(sK0,sK1)) | ~r2_hidden(X2,sK0) | ~v1_xboole_0(k3_subset_1(sK0,sK1))) )),
% 1.59/0.58    inference(resolution,[],[f94,f38])).
% 1.59/0.58  fof(f94,plain,(
% 1.59/0.58    ( ! [X2] : (r2_hidden(X2,k3_subset_1(sK0,sK1)) | r2_hidden(X2,k3_xboole_0(sK0,sK1)) | ~r2_hidden(X2,sK0)) )),
% 1.59/0.58    inference(superposition,[],[f55,f75])).
% 1.59/0.58  fof(f55,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f32])).
% 1.59/0.58  fof(f270,plain,(
% 1.59/0.58    ~spl6_1 | ~spl6_9),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f269])).
% 1.59/0.58  fof(f269,plain,(
% 1.59/0.58    $false | (~spl6_1 | ~spl6_9)),
% 1.59/0.58    inference(subsumption_resolution,[],[f65,f268])).
% 1.59/0.58  fof(f268,plain,(
% 1.59/0.58    ~v1_xboole_0(sK0) | ~spl6_9),
% 1.59/0.58    inference(resolution,[],[f151,f38])).
% 1.59/0.58  fof(f151,plain,(
% 1.59/0.58    r2_hidden(sK3(k3_subset_1(sK0,sK1)),sK0) | ~spl6_9),
% 1.59/0.58    inference(avatar_component_clause,[],[f116])).
% 1.59/0.58  fof(f116,plain,(
% 1.59/0.58    spl6_9 <=> r2_hidden(sK3(k3_subset_1(sK0,sK1)),sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.59/0.58  fof(f247,plain,(
% 1.59/0.58    spl6_10 | spl6_12),
% 1.59/0.58    inference(avatar_split_clause,[],[f241,f126,f120])).
% 1.59/0.58  fof(f241,plain,(
% 1.59/0.58    r2_hidden(sK4(k3_subset_1(sK0,sK1)),sK0) | k1_xboole_0 = k3_subset_1(sK0,sK1)),
% 1.59/0.58    inference(resolution,[],[f234,f40])).
% 1.59/0.58  fof(f40,plain,(
% 1.59/0.58    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.59/0.58    inference(cnf_transformation,[],[f25])).
% 1.59/0.58  fof(f25,plain,(
% 1.59/0.58    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f24])).
% 1.59/0.58  fof(f24,plain,(
% 1.59/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f12,plain,(
% 1.59/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.59/0.58    inference(ennf_transformation,[],[f4])).
% 1.59/0.58  fof(f4,axiom,(
% 1.59/0.58    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.59/0.58  fof(f246,plain,(
% 1.59/0.58    spl6_7 | spl6_9),
% 1.59/0.58    inference(avatar_split_clause,[],[f240,f116,f110])).
% 1.59/0.58  fof(f240,plain,(
% 1.59/0.58    r2_hidden(sK3(k3_subset_1(sK0,sK1)),sK0) | v1_xboole_0(k3_subset_1(sK0,sK1))),
% 1.59/0.58    inference(resolution,[],[f234,f39])).
% 1.59/0.58  fof(f39,plain,(
% 1.59/0.58    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f23])).
% 1.59/0.58  fof(f233,plain,(
% 1.59/0.58    ~spl6_14),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f231])).
% 1.59/0.58  fof(f231,plain,(
% 1.59/0.58    $false | ~spl6_14),
% 1.59/0.58    inference(subsumption_resolution,[],[f36,f229])).
% 1.59/0.58  fof(f229,plain,(
% 1.59/0.58    r2_hidden(sK2,sK1) | ~spl6_14),
% 1.59/0.58    inference(resolution,[],[f142,f59])).
% 1.59/0.58  fof(f59,plain,(
% 1.59/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 1.59/0.58    inference(equality_resolution,[],[f48])).
% 1.59/0.58  fof(f48,plain,(
% 1.59/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.59/0.58    inference(cnf_transformation,[],[f31])).
% 1.59/0.58  fof(f142,plain,(
% 1.59/0.58    r2_hidden(sK2,k3_xboole_0(sK0,sK1)) | ~spl6_14),
% 1.59/0.58    inference(avatar_component_clause,[],[f141])).
% 1.59/0.58  fof(f141,plain,(
% 1.59/0.58    spl6_14 <=> r2_hidden(sK2,k3_xboole_0(sK0,sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.59/0.58  fof(f36,plain,(
% 1.59/0.58    ~r2_hidden(sK2,sK1)),
% 1.59/0.58    inference(cnf_transformation,[],[f19])).
% 1.59/0.58  fof(f224,plain,(
% 1.59/0.58    ~spl6_1 | spl6_23 | ~spl6_10),
% 1.59/0.58    inference(avatar_split_clause,[],[f217,f120,f222,f64])).
% 1.59/0.58  fof(f217,plain,(
% 1.59/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~v1_xboole_0(sK0)) ) | ~spl6_10),
% 1.59/0.58    inference(resolution,[],[f160,f38])).
% 1.59/0.58  fof(f160,plain,(
% 1.59/0.58    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_10),
% 1.59/0.58    inference(backward_demodulation,[],[f100,f121])).
% 1.59/0.58  fof(f143,plain,(
% 1.59/0.58    ~spl6_2 | spl6_14),
% 1.59/0.58    inference(avatar_split_clause,[],[f132,f141,f67])).
% 1.59/0.58  fof(f132,plain,(
% 1.59/0.58    r2_hidden(sK2,k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK2,sK0)),
% 1.59/0.58    inference(resolution,[],[f94,f37])).
% 1.59/0.58  fof(f37,plain,(
% 1.59/0.58    ~r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 1.59/0.58    inference(cnf_transformation,[],[f19])).
% 1.59/0.58  % SZS output end Proof for theBenchmark
% 1.59/0.58  % (1889)------------------------------
% 1.59/0.58  % (1889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (1889)Termination reason: Refutation
% 1.59/0.58  
% 1.59/0.58  % (1889)Memory used [KB]: 11001
% 1.59/0.58  % (1889)Time elapsed: 0.130 s
% 1.59/0.58  % (1889)------------------------------
% 1.59/0.58  % (1889)------------------------------
% 1.59/0.58  % (1902)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.59/0.58  % (1886)Success in time 0.217 s
%------------------------------------------------------------------------------
