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
% DateTime   : Thu Dec  3 12:59:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 284 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  379 (1498 expanded)
%              Number of equality atoms :  156 ( 788 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f174,f184,f186,f188,f236,f247,f268,f287,f301,f338,f349,f355,f363])).

fof(f363,plain,
    ( ~ spl5_19
    | ~ spl5_33 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl5_19
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f83,f359])).

fof(f359,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl5_19
    | ~ spl5_33 ),
    inference(trivial_inequality_removal,[],[f358])).

fof(f358,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl5_19
    | ~ spl5_33 ),
    inference(superposition,[],[f232,f173])).

fof(f173,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_19
  <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f232,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl5_33
  <=> ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | ~ m1_subset_1(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f83,plain,(
    m1_subset_1(k2_mcart_1(sK4),sK2) ),
    inference(global_subsumption,[],[f55,f82])).

fof(f82,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(superposition,[],[f63,f73])).

fof(f73,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(global_subsumption,[],[f32,f33,f34,f69])).

% (31672)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f69,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f34,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X6
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X6
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f32,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f53,f43])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f55,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f30,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f355,plain,(
    ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f84,f229])).

fof(f229,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK4))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl5_32
  <=> sK3 = k2_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f84,plain,(
    sK3 != k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f35,f72])).

fof(f72,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(global_subsumption,[],[f32,f33,f34,f68])).

fof(f68,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f55,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f43])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f349,plain,
    ( ~ spl5_1
    | spl5_31 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | ~ spl5_1
    | spl5_31 ),
    inference(subsumption_resolution,[],[f344,f342])).

fof(f342,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | spl5_31 ),
    inference(resolution,[],[f226,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f226,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | spl5_31 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl5_31
  <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f344,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f304,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f304,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f76,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_1
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f338,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f337,f78,f75])).

fof(f78,plain,
    ( spl5_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f337,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f55,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f301,plain,
    ( ~ spl5_30
    | ~ spl5_31
    | spl5_32
    | spl5_33
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f299,f182,f231,f228,f225,f222])).

fof(f222,plain,
    ( spl5_30
  <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f182,plain,
    ( spl5_21
  <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f299,plain,
    ( ! [X1] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X1)
        | sK3 = k2_mcart_1(k1_mcart_1(sK4))
        | ~ m1_subset_1(X1,sK2)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) )
    | ~ spl5_21 ),
    inference(superposition,[],[f54,f183])).

fof(f183,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f54,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X6
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f31,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f287,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f33,f124])).

fof(f124,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f268,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f32,f121])).

fof(f121,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f247,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f34,f127])).

fof(f127,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl5_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f236,plain,
    ( ~ spl5_1
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl5_1
    | spl5_30 ),
    inference(subsumption_resolution,[],[f175,f234])).

fof(f234,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | spl5_30 ),
    inference(resolution,[],[f223,f39])).

fof(f223,plain,
    ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f222])).

fof(f175,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f165,f44])).

fof(f165,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f76,f44])).

fof(f188,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl5_18 ),
    inference(resolution,[],[f170,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f170,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl5_18
  <=> v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f186,plain,(
    spl5_20 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl5_20 ),
    inference(resolution,[],[f180,f37])).

fof(f180,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_20
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f184,plain,
    ( ~ spl5_20
    | spl5_21
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f177,f75,f182,f179])).

fof(f177,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f165,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f174,plain,
    ( ~ spl5_18
    | spl5_19
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f167,f75,f172,f169])).

fof(f167,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f76,f38])).

fof(f140,plain,
    ( spl5_7
    | spl5_8
    | spl5_9
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f118,f78,f126,f123,f120])).

fof(f118,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(superposition,[],[f59,f93])).

fof(f93,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f81,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f81,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = X0 )
    | ~ spl5_2 ),
    inference(resolution,[],[f79,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f79,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:45:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (31662)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (31662)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (31682)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (31664)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (31661)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (31674)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (31673)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f364,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f140,f174,f184,f186,f188,f236,f247,f268,f287,f301,f338,f349,f355,f363])).
% 0.21/0.52  fof(f363,plain,(
% 0.21/0.52    ~spl5_19 | ~spl5_33),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f361])).
% 0.21/0.52  fof(f361,plain,(
% 0.21/0.52    $false | (~spl5_19 | ~spl5_33)),
% 0.21/0.52    inference(subsumption_resolution,[],[f83,f359])).
% 0.21/0.52  fof(f359,plain,(
% 0.21/0.52    ~m1_subset_1(k2_mcart_1(sK4),sK2) | (~spl5_19 | ~spl5_33)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f358])).
% 0.21/0.52  fof(f358,plain,(
% 0.21/0.52    sK4 != sK4 | ~m1_subset_1(k2_mcart_1(sK4),sK2) | (~spl5_19 | ~spl5_33)),
% 0.21/0.52    inference(superposition,[],[f232,f173])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl5_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    spl5_19 <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(X0,sK2)) ) | ~spl5_33),
% 0.21/0.52    inference(avatar_component_clause,[],[f231])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    spl5_33 <=> ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(X0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(sK4),sK2)),
% 0.21/0.52    inference(global_subsumption,[],[f55,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(sK4),sK2) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.52    inference(superposition,[],[f63,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.52    inference(global_subsumption,[],[f32,f33,f34,f69])).
% 0.21/0.52  % (31672)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(resolution,[],[f55,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f52,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    k1_xboole_0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 1.23/0.52  fof(f14,negated_conjecture,(
% 1.23/0.52    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.23/0.52    inference(negated_conjecture,[],[f13])).
% 1.23/0.52  fof(f13,conjecture,(
% 1.23/0.52    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).
% 1.23/0.52  fof(f33,plain,(
% 1.23/0.52    k1_xboole_0 != sK1),
% 1.23/0.52    inference(cnf_transformation,[],[f27])).
% 1.23/0.52  fof(f32,plain,(
% 1.23/0.52    k1_xboole_0 != sK0),
% 1.23/0.52    inference(cnf_transformation,[],[f27])).
% 1.23/0.52  fof(f63,plain,(
% 1.23/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.23/0.52    inference(definition_unfolding,[],[f53,f43])).
% 1.23/0.52  fof(f53,plain,(
% 1.23/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f25])).
% 1.23/0.52  fof(f25,plain,(
% 1.23/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.23/0.52    inference(ennf_transformation,[],[f8])).
% 1.23/0.52  fof(f8,axiom,(
% 1.23/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 1.23/0.52  fof(f55,plain,(
% 1.23/0.52    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.23/0.52    inference(definition_unfolding,[],[f30,f43])).
% 1.23/0.52  fof(f30,plain,(
% 1.23/0.52    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.23/0.52    inference(cnf_transformation,[],[f27])).
% 1.23/0.52  fof(f355,plain,(
% 1.23/0.52    ~spl5_32),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f351])).
% 1.23/0.52  fof(f351,plain,(
% 1.23/0.52    $false | ~spl5_32),
% 1.23/0.52    inference(subsumption_resolution,[],[f84,f229])).
% 1.23/0.52  fof(f229,plain,(
% 1.23/0.52    sK3 = k2_mcart_1(k1_mcart_1(sK4)) | ~spl5_32),
% 1.23/0.52    inference(avatar_component_clause,[],[f228])).
% 1.23/0.52  fof(f228,plain,(
% 1.23/0.52    spl5_32 <=> sK3 = k2_mcart_1(k1_mcart_1(sK4))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.23/0.52  fof(f84,plain,(
% 1.23/0.52    sK3 != k2_mcart_1(k1_mcart_1(sK4))),
% 1.23/0.52    inference(superposition,[],[f35,f72])).
% 1.23/0.52  fof(f72,plain,(
% 1.23/0.52    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 1.23/0.52    inference(global_subsumption,[],[f32,f33,f34,f68])).
% 1.23/0.52  fof(f68,plain,(
% 1.23/0.52    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.23/0.52    inference(resolution,[],[f55,f61])).
% 1.23/0.52  fof(f61,plain,(
% 1.23/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(definition_unfolding,[],[f51,f43])).
% 1.23/0.52  fof(f51,plain,(
% 1.23/0.52    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f24])).
% 1.23/0.52  fof(f35,plain,(
% 1.23/0.52    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 1.23/0.52    inference(cnf_transformation,[],[f27])).
% 1.23/0.52  fof(f349,plain,(
% 1.23/0.52    ~spl5_1 | spl5_31),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f348])).
% 1.23/0.52  fof(f348,plain,(
% 1.23/0.52    $false | (~spl5_1 | spl5_31)),
% 1.23/0.52    inference(subsumption_resolution,[],[f344,f342])).
% 1.23/0.52  fof(f342,plain,(
% 1.23/0.52    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | spl5_31),
% 1.23/0.52    inference(resolution,[],[f226,f39])).
% 1.23/0.52  fof(f39,plain,(
% 1.23/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f19,plain,(
% 1.23/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.23/0.52    inference(ennf_transformation,[],[f3])).
% 1.23/0.52  fof(f3,axiom,(
% 1.23/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.23/0.52  fof(f226,plain,(
% 1.23/0.52    ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | spl5_31),
% 1.23/0.52    inference(avatar_component_clause,[],[f225])).
% 1.23/0.52  fof(f225,plain,(
% 1.23/0.52    spl5_31 <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.23/0.52  fof(f344,plain,(
% 1.23/0.52    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl5_1),
% 1.23/0.52    inference(resolution,[],[f304,f45])).
% 1.23/0.52  fof(f45,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f23])).
% 1.23/0.52  fof(f23,plain,(
% 1.23/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.23/0.52    inference(ennf_transformation,[],[f9])).
% 1.23/0.52  fof(f9,axiom,(
% 1.23/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.23/0.52  fof(f304,plain,(
% 1.23/0.52    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_1),
% 1.23/0.52    inference(resolution,[],[f76,f44])).
% 1.23/0.52  fof(f44,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f23])).
% 1.23/0.52  fof(f76,plain,(
% 1.23/0.52    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_1),
% 1.23/0.52    inference(avatar_component_clause,[],[f75])).
% 1.23/0.52  fof(f75,plain,(
% 1.23/0.52    spl5_1 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.23/0.52  fof(f338,plain,(
% 1.23/0.52    spl5_1 | spl5_2),
% 1.23/0.52    inference(avatar_split_clause,[],[f337,f78,f75])).
% 1.23/0.52  fof(f78,plain,(
% 1.23/0.52    spl5_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.23/0.52  fof(f337,plain,(
% 1.23/0.52    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.23/0.52    inference(resolution,[],[f55,f40])).
% 1.23/0.52  fof(f40,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f21])).
% 1.23/0.52  fof(f21,plain,(
% 1.23/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.23/0.52    inference(flattening,[],[f20])).
% 1.23/0.52  fof(f20,plain,(
% 1.23/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.23/0.52    inference(ennf_transformation,[],[f4])).
% 1.23/0.52  fof(f4,axiom,(
% 1.23/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.23/0.52  fof(f301,plain,(
% 1.23/0.52    ~spl5_30 | ~spl5_31 | spl5_32 | spl5_33 | ~spl5_21),
% 1.23/0.52    inference(avatar_split_clause,[],[f299,f182,f231,f228,f225,f222])).
% 1.23/0.52  fof(f222,plain,(
% 1.23/0.52    spl5_30 <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.23/0.52  fof(f182,plain,(
% 1.23/0.52    spl5_21 <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.23/0.52  fof(f299,plain,(
% 1.23/0.52    ( ! [X1] : (sK4 != k4_tarski(k1_mcart_1(sK4),X1) | sK3 = k2_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(X1,sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)) ) | ~spl5_21),
% 1.23/0.52    inference(superposition,[],[f54,f183])).
% 1.23/0.52  fof(f183,plain,(
% 1.23/0.52    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl5_21),
% 1.23/0.52    inference(avatar_component_clause,[],[f182])).
% 1.23/0.52  fof(f54,plain,(
% 1.23/0.52    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X6 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.23/0.52    inference(definition_unfolding,[],[f31,f42])).
% 1.23/0.52  fof(f42,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f6])).
% 1.23/0.52  fof(f6,axiom,(
% 1.23/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.23/0.52  fof(f31,plain,(
% 1.23/0.52    ( ! [X6,X7,X5] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f27])).
% 1.23/0.52  fof(f287,plain,(
% 1.23/0.52    ~spl5_8),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f282])).
% 1.23/0.52  fof(f282,plain,(
% 1.23/0.52    $false | ~spl5_8),
% 1.23/0.52    inference(subsumption_resolution,[],[f33,f124])).
% 1.23/0.52  fof(f124,plain,(
% 1.23/0.52    k1_xboole_0 = sK1 | ~spl5_8),
% 1.23/0.52    inference(avatar_component_clause,[],[f123])).
% 1.23/0.52  fof(f123,plain,(
% 1.23/0.52    spl5_8 <=> k1_xboole_0 = sK1),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.23/0.52  fof(f268,plain,(
% 1.23/0.52    ~spl5_7),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f259])).
% 1.23/0.52  fof(f259,plain,(
% 1.23/0.52    $false | ~spl5_7),
% 1.23/0.52    inference(subsumption_resolution,[],[f32,f121])).
% 1.23/0.52  fof(f121,plain,(
% 1.23/0.52    k1_xboole_0 = sK0 | ~spl5_7),
% 1.23/0.52    inference(avatar_component_clause,[],[f120])).
% 1.23/0.52  fof(f120,plain,(
% 1.23/0.52    spl5_7 <=> k1_xboole_0 = sK0),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.23/0.52  fof(f247,plain,(
% 1.23/0.52    ~spl5_9),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f237])).
% 1.23/0.52  fof(f237,plain,(
% 1.23/0.52    $false | ~spl5_9),
% 1.23/0.52    inference(subsumption_resolution,[],[f34,f127])).
% 1.23/0.52  fof(f127,plain,(
% 1.23/0.52    k1_xboole_0 = sK2 | ~spl5_9),
% 1.23/0.52    inference(avatar_component_clause,[],[f126])).
% 1.23/0.52  fof(f126,plain,(
% 1.23/0.52    spl5_9 <=> k1_xboole_0 = sK2),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.23/0.52  fof(f236,plain,(
% 1.23/0.52    ~spl5_1 | spl5_30),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f235])).
% 1.23/0.52  fof(f235,plain,(
% 1.23/0.52    $false | (~spl5_1 | spl5_30)),
% 1.23/0.52    inference(subsumption_resolution,[],[f175,f234])).
% 1.23/0.52  fof(f234,plain,(
% 1.23/0.52    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | spl5_30),
% 1.23/0.52    inference(resolution,[],[f223,f39])).
% 1.23/0.52  fof(f223,plain,(
% 1.23/0.52    ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | spl5_30),
% 1.23/0.52    inference(avatar_component_clause,[],[f222])).
% 1.23/0.52  fof(f175,plain,(
% 1.23/0.52    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl5_1),
% 1.23/0.52    inference(resolution,[],[f165,f44])).
% 1.23/0.52  fof(f165,plain,(
% 1.23/0.52    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_1),
% 1.23/0.52    inference(resolution,[],[f76,f44])).
% 1.23/0.52  fof(f188,plain,(
% 1.23/0.52    spl5_18),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f187])).
% 1.23/0.52  fof(f187,plain,(
% 1.23/0.52    $false | spl5_18),
% 1.23/0.52    inference(resolution,[],[f170,f37])).
% 1.23/0.52  fof(f37,plain,(
% 1.23/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f5])).
% 1.23/0.52  fof(f5,axiom,(
% 1.23/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.23/0.52  fof(f170,plain,(
% 1.23/0.52    ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl5_18),
% 1.23/0.52    inference(avatar_component_clause,[],[f169])).
% 1.23/0.52  fof(f169,plain,(
% 1.23/0.52    spl5_18 <=> v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.23/0.52  fof(f186,plain,(
% 1.23/0.52    spl5_20),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f185])).
% 1.23/0.52  fof(f185,plain,(
% 1.23/0.52    $false | spl5_20),
% 1.23/0.52    inference(resolution,[],[f180,f37])).
% 1.23/0.52  fof(f180,plain,(
% 1.23/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl5_20),
% 1.23/0.52    inference(avatar_component_clause,[],[f179])).
% 1.23/0.52  fof(f179,plain,(
% 1.23/0.52    spl5_20 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.23/0.52  fof(f184,plain,(
% 1.23/0.52    ~spl5_20 | spl5_21 | ~spl5_1),
% 1.23/0.52    inference(avatar_split_clause,[],[f177,f75,f182,f179])).
% 1.23/0.52  fof(f177,plain,(
% 1.23/0.52    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl5_1),
% 1.23/0.52    inference(resolution,[],[f165,f38])).
% 1.23/0.52  fof(f38,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f18,plain,(
% 1.23/0.52    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.23/0.52    inference(flattening,[],[f17])).
% 1.23/0.52  fof(f17,plain,(
% 1.23/0.52    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.23/0.52    inference(ennf_transformation,[],[f10])).
% 1.23/0.52  fof(f10,axiom,(
% 1.23/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.23/0.52  fof(f174,plain,(
% 1.23/0.52    ~spl5_18 | spl5_19 | ~spl5_1),
% 1.23/0.52    inference(avatar_split_clause,[],[f167,f75,f172,f169])).
% 1.23/0.52  fof(f167,plain,(
% 1.23/0.52    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_1),
% 1.23/0.52    inference(resolution,[],[f76,f38])).
% 1.23/0.52  fof(f140,plain,(
% 1.23/0.52    spl5_7 | spl5_8 | spl5_9 | ~spl5_2),
% 1.23/0.52    inference(avatar_split_clause,[],[f118,f78,f126,f123,f120])).
% 1.23/0.52  fof(f118,plain,(
% 1.23/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_2),
% 1.23/0.52    inference(trivial_inequality_removal,[],[f109])).
% 1.23/0.52  fof(f109,plain,(
% 1.23/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_2),
% 1.23/0.52    inference(superposition,[],[f59,f93])).
% 1.23/0.52  fof(f93,plain,(
% 1.23/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl5_2),
% 1.23/0.52    inference(resolution,[],[f81,f36])).
% 1.23/0.52  fof(f36,plain,(
% 1.23/0.52    v1_xboole_0(k1_xboole_0)),
% 1.23/0.52    inference(cnf_transformation,[],[f1])).
% 1.23/0.52  fof(f1,axiom,(
% 1.23/0.52    v1_xboole_0(k1_xboole_0)),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.23/0.52  fof(f81,plain,(
% 1.23/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = X0) ) | ~spl5_2),
% 1.23/0.52    inference(resolution,[],[f79,f41])).
% 1.23/0.52  fof(f41,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f22])).
% 1.23/0.52  fof(f22,plain,(
% 1.23/0.52    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f2])).
% 1.23/0.52  fof(f2,axiom,(
% 1.23/0.52    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.23/0.52  fof(f79,plain,(
% 1.23/0.52    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_2),
% 1.23/0.52    inference(avatar_component_clause,[],[f78])).
% 1.23/0.52  fof(f59,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(definition_unfolding,[],[f46,f43])).
% 1.23/0.52  fof(f46,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f29])).
% 1.23/0.52  fof(f29,plain,(
% 1.23/0.52    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.23/0.52    inference(flattening,[],[f28])).
% 1.23/0.52  fof(f28,plain,(
% 1.23/0.52    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.23/0.52    inference(nnf_transformation,[],[f11])).
% 1.23/0.52  fof(f11,axiom,(
% 1.23/0.52    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 1.23/0.52  % SZS output end Proof for theBenchmark
% 1.23/0.52  % (31682)Refutation not found, incomplete strategy% (31682)------------------------------
% 1.23/0.52  % (31682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (31662)------------------------------
% 1.23/0.52  % (31662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (31662)Termination reason: Refutation
% 1.23/0.52  
% 1.23/0.52  % (31662)Memory used [KB]: 10874
% 1.23/0.52  % (31662)Time elapsed: 0.102 s
% 1.23/0.52  % (31662)------------------------------
% 1.23/0.52  % (31662)------------------------------
% 1.23/0.53  % (31659)Success in time 0.164 s
%------------------------------------------------------------------------------
