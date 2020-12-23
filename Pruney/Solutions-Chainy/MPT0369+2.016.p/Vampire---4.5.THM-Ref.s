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
% DateTime   : Thu Dec  3 12:45:25 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   91 (1557 expanded)
%              Number of leaves         :   14 ( 507 expanded)
%              Depth                    :   26
%              Number of atoms          :  296 (7960 expanded)
%              Number of equality atoms :   59 (1288 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f385,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f150,f384])).

fof(f384,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f36,f359])).

fof(f359,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_1 ),
    inference(resolution,[],[f346,f79])).

fof(f79,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f346,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f337,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
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

fof(f337,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK5(k1_xboole_0,X6,X7),X7)
      | k1_xboole_0 = X7 ) ),
    inference(backward_demodulation,[],[f271,f298])).

fof(f298,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(resolution,[],[f269,f288])).

% (20985)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f288,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(global_subsumption,[],[f287])).

fof(f287,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(global_subsumption,[],[f75,f143,f285])).

fof(f285,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f242,f43])).

fof(f242,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f106,f224])).

fof(f224,plain,(
    k1_xboole_0 = k3_subset_1(sK0,sK1) ),
    inference(superposition,[],[f197,f62])).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f197,plain,(
    ! [X2] : k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X2)) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X2] :
      ( k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X2))
      | k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X2)) ) ),
    inference(resolution,[],[f180,f174])).

fof(f174,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3,k3_subset_1(sK0,sK1)),X2)
      | k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) ) ),
    inference(global_subsumption,[],[f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,k3_subset_1(sK0,sK1)),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK0,sK1) ) ),
    inference(global_subsumption,[],[f75,f143,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,k3_subset_1(sK0,sK1)),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK0,sK1)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f119,f43])).

fof(f119,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3,k3_subset_1(sK0,sK1)),sK0)
      | r2_hidden(sK5(X2,X3,k3_subset_1(sK0,sK1)),X2)
      | k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f106,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f59,f45])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

% (20976)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f180,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK5(X4,X5,k3_subset_1(sK0,sK1)),X5)
      | k3_subset_1(sK0,sK1) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ) ),
    inference(global_subsumption,[],[f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,k3_subset_1(sK0,sK1)),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK0,sK1) ) ),
    inference(global_subsumption,[],[f75,f143,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,k3_subset_1(sK0,sK1)),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK0,sK1)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f120,f43])).

fof(f120,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(X4,X5,k3_subset_1(sK0,sK1)),sK0)
      | ~ r2_hidden(sK5(X4,X5,k3_subset_1(sK0,sK1)),X5)
      | k3_subset_1(sK0,sK1) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f106,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f60,f45])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK0,sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f74,f89])).

fof(f89,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f37,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f45])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
    & ~ r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19,f18,f17])).

fof(f17,plain,
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

fof(f18,plain,
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

fof(f19,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,k3_subset_1(sK0,sK1))
        & ~ r2_hidden(X2,sK1)
        & m1_subset_1(X2,sK0) )
   => ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
      & ~ r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f45])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f143,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(global_subsumption,[],[f39,f138])).

fof(f138,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f108,f40])).

fof(f40,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f108,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_subset_1(sK0,sK1))
      | r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f72,f89])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f58,f45])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f39,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f38,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f269,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3,k1_xboole_0),X2)
      | k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X3)) ) ),
    inference(forward_demodulation,[],[f253,f224])).

fof(f253,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3,k1_xboole_0),X2)
      | k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) ) ),
    inference(backward_demodulation,[],[f174,f224])).

fof(f271,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK5(k1_xboole_0,X6,X7),X7)
      | k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X6)) = X7 ) ),
    inference(forward_demodulation,[],[f256,f224])).

fof(f256,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK5(k1_xboole_0,X6,X7),X7)
      | k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),X6)) = X7 ) ),
    inference(backward_demodulation,[],[f222,f224])).

fof(f222,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK5(k3_subset_1(sK0,sK1),X6,X7),X7)
      | k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),X6)) = X7 ) ),
    inference(global_subsumption,[],[f213])).

fof(f213,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1)
      | k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),X0)) = X1 ) ),
    inference(global_subsumption,[],[f75,f143,f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1)
      | k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),X0)) = X1
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f121,f43])).

fof(f121,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK5(k3_subset_1(sK0,sK1),X6,X7),sK0)
      | r2_hidden(sK5(k3_subset_1(sK0,sK1),X6,X7),X7)
      | k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),X6)) = X7 ) ),
    inference(resolution,[],[f106,f68])).

fof(f36,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f150,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f82,f143])).

fof(f82,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f83,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f75,f81,f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:48:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.55  % (20970)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (20972)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.58  % (20988)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (20978)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (20980)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.58  % (20998)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.61/0.60  % (20974)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.61/0.60  % (20973)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.61/0.60  % (20972)Refutation found. Thanks to Tanya!
% 1.61/0.60  % SZS status Theorem for theBenchmark
% 1.61/0.60  % SZS output start Proof for theBenchmark
% 1.61/0.60  fof(f385,plain,(
% 1.61/0.60    $false),
% 1.61/0.60    inference(avatar_sat_refutation,[],[f83,f150,f384])).
% 1.61/0.60  fof(f384,plain,(
% 1.61/0.60    ~spl6_1),
% 1.61/0.60    inference(avatar_contradiction_clause,[],[f370])).
% 1.61/0.60  fof(f370,plain,(
% 1.61/0.60    $false | ~spl6_1),
% 1.61/0.60    inference(subsumption_resolution,[],[f36,f359])).
% 1.61/0.60  fof(f359,plain,(
% 1.61/0.60    k1_xboole_0 = sK0 | ~spl6_1),
% 1.61/0.60    inference(resolution,[],[f346,f79])).
% 1.61/0.60  fof(f79,plain,(
% 1.61/0.60    v1_xboole_0(sK0) | ~spl6_1),
% 1.61/0.60    inference(avatar_component_clause,[],[f78])).
% 1.61/0.60  fof(f78,plain,(
% 1.61/0.60    spl6_1 <=> v1_xboole_0(sK0)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.61/0.60  fof(f346,plain,(
% 1.61/0.60    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 1.61/0.60    inference(resolution,[],[f337,f43])).
% 1.61/0.60  fof(f43,plain,(
% 1.61/0.60    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f24])).
% 1.61/0.60  fof(f24,plain,(
% 1.61/0.60    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.61/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 1.61/0.60  fof(f23,plain,(
% 1.61/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.61/0.60    introduced(choice_axiom,[])).
% 1.61/0.60  fof(f22,plain,(
% 1.61/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.61/0.60    inference(rectify,[],[f21])).
% 1.61/0.60  fof(f21,plain,(
% 1.61/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.61/0.60    inference(nnf_transformation,[],[f1])).
% 1.61/0.60  fof(f1,axiom,(
% 1.61/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.61/0.60  fof(f337,plain,(
% 1.61/0.60    ( ! [X6,X7] : (r2_hidden(sK5(k1_xboole_0,X6,X7),X7) | k1_xboole_0 = X7) )),
% 1.61/0.60    inference(backward_demodulation,[],[f271,f298])).
% 1.61/0.60  fof(f298,plain,(
% 1.61/0.60    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))) )),
% 1.61/0.60    inference(resolution,[],[f269,f288])).
% 1.61/0.60  % (20985)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.61/0.60  fof(f288,plain,(
% 1.61/0.60    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.61/0.60    inference(global_subsumption,[],[f287])).
% 1.61/0.60  fof(f287,plain,(
% 1.61/0.60    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.61/0.60    inference(global_subsumption,[],[f75,f143,f285])).
% 1.61/0.60  fof(f285,plain,(
% 1.61/0.60    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~v1_xboole_0(sK0)) )),
% 1.61/0.60    inference(resolution,[],[f242,f43])).
% 1.61/0.60  fof(f242,plain,(
% 1.61/0.60    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.61/0.60    inference(backward_demodulation,[],[f106,f224])).
% 1.61/0.60  fof(f224,plain,(
% 1.61/0.60    k1_xboole_0 = k3_subset_1(sK0,sK1)),
% 1.61/0.60    inference(superposition,[],[f197,f62])).
% 1.61/0.60  fof(f62,plain,(
% 1.61/0.60    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.61/0.60    inference(definition_unfolding,[],[f42,f45])).
% 1.61/0.60  fof(f45,plain,(
% 1.61/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.61/0.60    inference(cnf_transformation,[],[f5])).
% 1.61/0.60  fof(f5,axiom,(
% 1.61/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.61/0.60  fof(f42,plain,(
% 1.61/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.61/0.60    inference(cnf_transformation,[],[f7])).
% 1.61/0.60  fof(f7,axiom,(
% 1.61/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.61/0.60  fof(f197,plain,(
% 1.61/0.60    ( ! [X2] : (k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X2))) )),
% 1.61/0.60    inference(duplicate_literal_removal,[],[f183])).
% 1.61/0.60  fof(f183,plain,(
% 1.61/0.60    ( ! [X2] : (k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X2)) | k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X2))) )),
% 1.61/0.60    inference(resolution,[],[f180,f174])).
% 1.61/0.60  fof(f174,plain,(
% 1.61/0.60    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3,k3_subset_1(sK0,sK1)),X2) | k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.61/0.60    inference(global_subsumption,[],[f171])).
% 1.61/0.60  fof(f171,plain,(
% 1.61/0.60    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,k3_subset_1(sK0,sK1)),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK0,sK1)) )),
% 1.61/0.60    inference(global_subsumption,[],[f75,f143,f163])).
% 1.61/0.60  fof(f163,plain,(
% 1.61/0.60    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,k3_subset_1(sK0,sK1)),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK0,sK1) | ~v1_xboole_0(sK0)) )),
% 1.61/0.60    inference(resolution,[],[f119,f43])).
% 1.61/0.60  fof(f119,plain,(
% 1.61/0.60    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3,k3_subset_1(sK0,sK1)),sK0) | r2_hidden(sK5(X2,X3,k3_subset_1(sK0,sK1)),X2) | k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.61/0.60    inference(resolution,[],[f106,f68])).
% 1.61/0.60  fof(f68,plain,(
% 1.61/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.61/0.60    inference(definition_unfolding,[],[f59,f45])).
% 1.61/0.60  fof(f59,plain,(
% 1.61/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f35])).
% 1.61/0.60  fof(f35,plain,(
% 1.61/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.61/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 1.61/0.60  fof(f34,plain,(
% 1.61/0.60    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.61/0.60    introduced(choice_axiom,[])).
% 1.61/0.60  fof(f33,plain,(
% 1.61/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.61/0.60    inference(rectify,[],[f32])).
% 1.61/0.60  % (20976)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.61/0.60  fof(f32,plain,(
% 1.61/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.61/0.60    inference(flattening,[],[f31])).
% 1.61/0.60  fof(f31,plain,(
% 1.61/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.61/0.60    inference(nnf_transformation,[],[f3])).
% 1.61/0.60  fof(f3,axiom,(
% 1.61/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.61/0.60  fof(f180,plain,(
% 1.61/0.60    ( ! [X4,X5] : (~r2_hidden(sK5(X4,X5,k3_subset_1(sK0,sK1)),X5) | k3_subset_1(sK0,sK1) = k5_xboole_0(X4,k3_xboole_0(X4,X5))) )),
% 1.61/0.60    inference(global_subsumption,[],[f173])).
% 1.61/0.60  fof(f173,plain,(
% 1.61/0.60    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1,k3_subset_1(sK0,sK1)),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK0,sK1)) )),
% 1.61/0.60    inference(global_subsumption,[],[f75,f143,f172])).
% 1.61/0.60  fof(f172,plain,(
% 1.61/0.60    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1,k3_subset_1(sK0,sK1)),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK0,sK1) | ~v1_xboole_0(sK0)) )),
% 1.61/0.60    inference(resolution,[],[f120,f43])).
% 1.61/0.60  fof(f120,plain,(
% 1.61/0.60    ( ! [X4,X5] : (r2_hidden(sK5(X4,X5,k3_subset_1(sK0,sK1)),sK0) | ~r2_hidden(sK5(X4,X5,k3_subset_1(sK0,sK1)),X5) | k3_subset_1(sK0,sK1) = k5_xboole_0(X4,k3_xboole_0(X4,X5))) )),
% 1.61/0.60    inference(resolution,[],[f106,f67])).
% 1.61/0.60  fof(f67,plain,(
% 1.61/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.61/0.60    inference(definition_unfolding,[],[f60,f45])).
% 1.61/0.60  fof(f60,plain,(
% 1.61/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f35])).
% 1.61/0.60  fof(f106,plain,(
% 1.61/0.60    ( ! [X0] : (~r2_hidden(X0,k3_subset_1(sK0,sK1)) | r2_hidden(X0,sK0)) )),
% 1.61/0.60    inference(superposition,[],[f74,f89])).
% 1.61/0.60  fof(f89,plain,(
% 1.61/0.60    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.61/0.60    inference(resolution,[],[f37,f63])).
% 1.61/0.60  fof(f63,plain,(
% 1.61/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.61/0.60    inference(definition_unfolding,[],[f50,f45])).
% 1.61/0.60  fof(f50,plain,(
% 1.61/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.60    inference(cnf_transformation,[],[f15])).
% 1.61/0.60  fof(f15,plain,(
% 1.61/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.60    inference(ennf_transformation,[],[f9])).
% 1.61/0.60  fof(f9,axiom,(
% 1.61/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.61/0.60  fof(f37,plain,(
% 1.61/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.61/0.60    inference(cnf_transformation,[],[f20])).
% 1.61/0.60  fof(f20,plain,(
% 1.61/0.60    ((~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0),
% 1.61/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19,f18,f17])).
% 1.61/0.60  fof(f17,plain,(
% 1.61/0.60    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0) => (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0)),
% 1.61/0.60    introduced(choice_axiom,[])).
% 1.61/0.60  fof(f18,plain,(
% 1.61/0.60    ? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) => (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.61/0.60    introduced(choice_axiom,[])).
% 1.61/0.60  fof(f19,plain,(
% 1.61/0.60    ? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) => (~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0))),
% 1.61/0.60    introduced(choice_axiom,[])).
% 1.61/0.60  fof(f13,plain,(
% 1.61/0.60    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.61/0.60    inference(flattening,[],[f12])).
% 1.61/0.60  fof(f12,plain,(
% 1.61/0.60    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.61/0.60    inference(ennf_transformation,[],[f11])).
% 1.61/0.60  fof(f11,negated_conjecture,(
% 1.61/0.60    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.61/0.60    inference(negated_conjecture,[],[f10])).
% 1.61/0.60  fof(f10,conjecture,(
% 1.61/0.60    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 1.61/0.60  fof(f74,plain,(
% 1.61/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 1.61/0.60    inference(equality_resolution,[],[f71])).
% 1.61/0.60  fof(f71,plain,(
% 1.61/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.61/0.60    inference(definition_unfolding,[],[f56,f45])).
% 1.61/0.60  fof(f56,plain,(
% 1.61/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.61/0.60    inference(cnf_transformation,[],[f35])).
% 1.61/0.60  fof(f143,plain,(
% 1.61/0.60    ~r2_hidden(sK2,sK0)),
% 1.61/0.60    inference(global_subsumption,[],[f39,f138])).
% 1.61/0.60  fof(f138,plain,(
% 1.61/0.60    r2_hidden(sK2,sK1) | ~r2_hidden(sK2,sK0)),
% 1.61/0.60    inference(resolution,[],[f108,f40])).
% 1.61/0.60  fof(f40,plain,(
% 1.61/0.60    ~r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 1.61/0.60    inference(cnf_transformation,[],[f20])).
% 1.61/0.60  fof(f108,plain,(
% 1.61/0.60    ( ! [X2] : (r2_hidden(X2,k3_subset_1(sK0,sK1)) | r2_hidden(X2,sK1) | ~r2_hidden(X2,sK0)) )),
% 1.61/0.60    inference(superposition,[],[f72,f89])).
% 1.61/0.60  fof(f72,plain,(
% 1.61/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.61/0.60    inference(equality_resolution,[],[f69])).
% 1.61/0.60  fof(f69,plain,(
% 1.61/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.61/0.60    inference(definition_unfolding,[],[f58,f45])).
% 1.61/0.60  fof(f58,plain,(
% 1.61/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.61/0.60    inference(cnf_transformation,[],[f35])).
% 1.61/0.60  fof(f39,plain,(
% 1.61/0.60    ~r2_hidden(sK2,sK1)),
% 1.61/0.60    inference(cnf_transformation,[],[f20])).
% 1.61/0.60  fof(f75,plain,(
% 1.61/0.60    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 1.61/0.60    inference(resolution,[],[f38,f46])).
% 1.61/0.60  fof(f46,plain,(
% 1.61/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f25])).
% 1.61/0.60  fof(f25,plain,(
% 1.61/0.60    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.61/0.60    inference(nnf_transformation,[],[f14])).
% 1.61/0.60  fof(f14,plain,(
% 1.61/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.61/0.60    inference(ennf_transformation,[],[f8])).
% 1.61/0.60  fof(f8,axiom,(
% 1.61/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.61/0.60  fof(f38,plain,(
% 1.61/0.60    m1_subset_1(sK2,sK0)),
% 1.61/0.60    inference(cnf_transformation,[],[f20])).
% 1.61/0.60  fof(f269,plain,(
% 1.61/0.60    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3,k1_xboole_0),X2) | k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.61/0.60    inference(forward_demodulation,[],[f253,f224])).
% 1.61/0.60  fof(f253,plain,(
% 1.61/0.60    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3,k1_xboole_0),X2) | k3_subset_1(sK0,sK1) = k5_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.61/0.60    inference(backward_demodulation,[],[f174,f224])).
% 1.61/0.60  fof(f271,plain,(
% 1.61/0.60    ( ! [X6,X7] : (r2_hidden(sK5(k1_xboole_0,X6,X7),X7) | k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X6)) = X7) )),
% 1.61/0.60    inference(forward_demodulation,[],[f256,f224])).
% 1.61/0.60  fof(f256,plain,(
% 1.61/0.60    ( ! [X6,X7] : (r2_hidden(sK5(k1_xboole_0,X6,X7),X7) | k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),X6)) = X7) )),
% 1.61/0.60    inference(backward_demodulation,[],[f222,f224])).
% 1.61/0.60  fof(f222,plain,(
% 1.61/0.60    ( ! [X6,X7] : (r2_hidden(sK5(k3_subset_1(sK0,sK1),X6,X7),X7) | k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),X6)) = X7) )),
% 1.61/0.60    inference(global_subsumption,[],[f213])).
% 1.61/0.60  fof(f213,plain,(
% 1.61/0.60    ( ! [X0,X1] : (r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1) | k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),X0)) = X1) )),
% 1.61/0.60    inference(global_subsumption,[],[f75,f143,f203])).
% 1.61/0.60  fof(f203,plain,(
% 1.61/0.60    ( ! [X0,X1] : (r2_hidden(sK5(k3_subset_1(sK0,sK1),X0,X1),X1) | k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),X0)) = X1 | ~v1_xboole_0(sK0)) )),
% 1.61/0.60    inference(resolution,[],[f121,f43])).
% 1.61/0.60  fof(f121,plain,(
% 1.61/0.60    ( ! [X6,X7] : (r2_hidden(sK5(k3_subset_1(sK0,sK1),X6,X7),sK0) | r2_hidden(sK5(k3_subset_1(sK0,sK1),X6,X7),X7) | k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),X6)) = X7) )),
% 1.61/0.60    inference(resolution,[],[f106,f68])).
% 1.61/0.60  fof(f36,plain,(
% 1.61/0.60    k1_xboole_0 != sK0),
% 1.61/0.60    inference(cnf_transformation,[],[f20])).
% 1.61/0.60  fof(f150,plain,(
% 1.61/0.60    ~spl6_2),
% 1.61/0.60    inference(avatar_contradiction_clause,[],[f149])).
% 1.61/0.60  fof(f149,plain,(
% 1.61/0.60    $false | ~spl6_2),
% 1.61/0.60    inference(subsumption_resolution,[],[f82,f143])).
% 1.61/0.60  fof(f82,plain,(
% 1.61/0.60    r2_hidden(sK2,sK0) | ~spl6_2),
% 1.61/0.60    inference(avatar_component_clause,[],[f81])).
% 1.61/0.60  fof(f81,plain,(
% 1.61/0.60    spl6_2 <=> r2_hidden(sK2,sK0)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.61/0.60  fof(f83,plain,(
% 1.61/0.60    spl6_1 | spl6_2),
% 1.61/0.60    inference(avatar_split_clause,[],[f75,f81,f78])).
% 1.61/0.60  % SZS output end Proof for theBenchmark
% 1.61/0.60  % (20972)------------------------------
% 1.61/0.60  % (20972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.60  % (20972)Termination reason: Refutation
% 1.61/0.60  
% 1.61/0.60  % (20972)Memory used [KB]: 11001
% 1.61/0.60  % (20972)Time elapsed: 0.160 s
% 1.61/0.60  % (20972)------------------------------
% 1.61/0.60  % (20972)------------------------------
% 1.61/0.60  % (20969)Success in time 0.236 s
%------------------------------------------------------------------------------
