%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 298 expanded)
%              Number of leaves         :   27 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  386 (1657 expanded)
%              Number of equality atoms :  154 ( 871 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f420,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f166,f174,f214,f260,f261,f262,f293,f299,f307,f314,f379,f391,f419])).

fof(f419,plain,(
    ~ spl5_30 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f33,f232])).

fof(f232,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl5_30
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f26])).

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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f391,plain,
    ( spl5_29
    | spl5_30
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f390,f77,f231,f228])).

fof(f228,plain,
    ( spl5_29
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f77,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f390,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f383])).

fof(f383,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl5_1 ),
    inference(superposition,[],[f46,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f379,plain,(
    ~ spl5_29 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f34,f229])).

fof(f229,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f228])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f314,plain,
    ( ~ spl5_2
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f114,f309])).

fof(f309,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(trivial_inequality_removal,[],[f308])).

fof(f308,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(superposition,[],[f204,f81])).

fof(f81,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_2
  <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f204,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl5_27
  <=> ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | ~ m1_subset_1(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f114,plain,(
    m1_subset_1(k2_mcart_1(sK4),sK2) ),
    inference(global_subsumption,[],[f59,f113])).

fof(f113,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(superposition,[],[f63,f74])).

fof(f74,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(global_subsumption,[],[f33,f34,f35,f68])).

fof(f68,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f59,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f56,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f35,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f57,f51])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f59,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f31,f51])).

fof(f31,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f307,plain,
    ( ~ spl5_24
    | ~ spl5_25
    | spl5_26
    | spl5_27
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f305,f155,f203,f200,f197,f194])).

fof(f194,plain,
    ( spl5_24
  <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f197,plain,
    ( spl5_25
  <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f200,plain,
    ( spl5_26
  <=> sK3 = k2_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f155,plain,
    ( spl5_18
  <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f305,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | sK3 = k2_mcart_1(k1_mcart_1(sK4))
        | ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) )
    | ~ spl5_18 ),
    inference(superposition,[],[f58,f156])).

fof(f156,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f58,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X6
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f32,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f32,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f299,plain,(
    ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f115,f201])).

fof(f201,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK4))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f200])).

fof(f115,plain,(
    sK3 != k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f36,f73])).

fof(f73,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(global_subsumption,[],[f33,f34,f35,f67])).

fof(f67,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f59,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f55,f51])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f293,plain,
    ( ~ spl5_4
    | spl5_25 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl5_4
    | spl5_25 ),
    inference(subsumption_resolution,[],[f285,f263])).

fof(f263,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | spl5_25 ),
    inference(resolution,[],[f198,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f198,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | spl5_25 ),
    inference(avatar_component_clause,[],[f197])).

fof(f285,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f280,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f280,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f88,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_4
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f262,plain,
    ( ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f258,f92,f84])).

fof(f84,plain,
    ( spl5_3
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f92,plain,
    ( spl5_5
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f258,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f59,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f261,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f257,f87,f84])).

fof(f257,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f260,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f259,f80,f77])).

fof(f259,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(global_subsumption,[],[f75])).

fof(f75,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(global_subsumption,[],[f35,f69])).

fof(f69,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f59,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f214,plain,
    ( ~ spl5_4
    | spl5_24 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl5_4
    | spl5_24 ),
    inference(subsumption_resolution,[],[f171,f206])).

fof(f206,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | spl5_24 ),
    inference(resolution,[],[f195,f45])).

fof(f195,plain,
    ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | spl5_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f171,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f167,f52])).

fof(f167,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f88,f52])).

fof(f174,plain,
    ( ~ spl5_17
    | spl5_18
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f173,f87,f155,f152])).

fof(f152,plain,
    ( spl5_17
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f173,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f167,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f166,plain,
    ( ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f96,f93])).

fof(f93,plain,
    ( v1_xboole_0(sK4)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f96,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl5_2 ),
    inference(superposition,[],[f37,f81])).

fof(f37,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_zfmisc_1)).

fof(f159,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl5_17 ),
    inference(resolution,[],[f153,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f153,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (13150)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.47  % (13158)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.47  % (13174)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.48  % (13150)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f420,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f159,f166,f174,f214,f260,f261,f262,f293,f299,f307,f314,f379,f391,f419])).
% 0.19/0.48  fof(f419,plain,(
% 0.19/0.48    ~spl5_30),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f409])).
% 0.19/0.49  fof(f409,plain,(
% 0.19/0.49    $false | ~spl5_30),
% 0.19/0.49    inference(subsumption_resolution,[],[f33,f232])).
% 0.19/0.49  fof(f232,plain,(
% 0.19/0.49    k1_xboole_0 = sK0 | ~spl5_30),
% 0.19/0.49    inference(avatar_component_clause,[],[f231])).
% 0.19/0.49  fof(f231,plain,(
% 0.19/0.49    spl5_30 <=> k1_xboole_0 = sK0),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    k1_xboole_0 != sK0),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.19/0.49    inference(flattening,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.19/0.49    inference(ennf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.19/0.49    inference(negated_conjecture,[],[f14])).
% 0.19/0.49  fof(f14,conjecture,(
% 0.19/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).
% 0.19/0.49  fof(f391,plain,(
% 0.19/0.49    spl5_29 | spl5_30 | ~spl5_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f390,f77,f231,f228])).
% 0.19/0.49  fof(f228,plain,(
% 0.19/0.49    spl5_29 <=> k1_xboole_0 = sK1),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.19/0.49  fof(f77,plain,(
% 0.19/0.49    spl5_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.49  fof(f390,plain,(
% 0.19/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl5_1),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f383])).
% 0.19/0.49  fof(f383,plain,(
% 0.19/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl5_1),
% 0.19/0.49    inference(superposition,[],[f46,f78])).
% 0.19/0.49  fof(f78,plain,(
% 0.19/0.49    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl5_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f77])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.49    inference(flattening,[],[f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.49    inference(nnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.49  fof(f379,plain,(
% 0.19/0.49    ~spl5_29),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f370])).
% 0.19/0.49  fof(f370,plain,(
% 0.19/0.49    $false | ~spl5_29),
% 0.19/0.49    inference(subsumption_resolution,[],[f34,f229])).
% 0.19/0.49  fof(f229,plain,(
% 0.19/0.49    k1_xboole_0 = sK1 | ~spl5_29),
% 0.19/0.49    inference(avatar_component_clause,[],[f228])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    k1_xboole_0 != sK1),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f314,plain,(
% 0.19/0.49    ~spl5_2 | ~spl5_27),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f310])).
% 0.19/0.49  fof(f310,plain,(
% 0.19/0.49    $false | (~spl5_2 | ~spl5_27)),
% 0.19/0.49    inference(subsumption_resolution,[],[f114,f309])).
% 0.19/0.49  fof(f309,plain,(
% 0.19/0.49    ~m1_subset_1(k2_mcart_1(sK4),sK2) | (~spl5_2 | ~spl5_27)),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f308])).
% 0.19/0.49  fof(f308,plain,(
% 0.19/0.49    sK4 != sK4 | ~m1_subset_1(k2_mcart_1(sK4),sK2) | (~spl5_2 | ~spl5_27)),
% 0.19/0.49    inference(superposition,[],[f204,f81])).
% 0.19/0.49  fof(f81,plain,(
% 0.19/0.49    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl5_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f80])).
% 0.19/0.49  fof(f80,plain,(
% 0.19/0.49    spl5_2 <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.49  fof(f204,plain,(
% 0.19/0.49    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(X0,sK2)) ) | ~spl5_27),
% 0.19/0.49    inference(avatar_component_clause,[],[f203])).
% 0.19/0.49  fof(f203,plain,(
% 0.19/0.49    spl5_27 <=> ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(X0,sK2))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.19/0.49  fof(f114,plain,(
% 0.19/0.49    m1_subset_1(k2_mcart_1(sK4),sK2)),
% 0.19/0.49    inference(global_subsumption,[],[f59,f113])).
% 0.19/0.49  fof(f113,plain,(
% 0.19/0.49    m1_subset_1(k2_mcart_1(sK4),sK2) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.19/0.49    inference(superposition,[],[f63,f74])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.19/0.49    inference(global_subsumption,[],[f33,f34,f35,f68])).
% 0.19/0.49  fof(f68,plain,(
% 0.19/0.49    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.19/0.49    inference(resolution,[],[f59,f60])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.49    inference(definition_unfolding,[],[f56,f51])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.19/0.49    inference(ennf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    k1_xboole_0 != sK2),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f63,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 0.19/0.49    inference(definition_unfolding,[],[f57,f51])).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 0.19/0.49  fof(f59,plain,(
% 0.19/0.49    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.19/0.49    inference(definition_unfolding,[],[f31,f51])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f307,plain,(
% 0.19/0.49    ~spl5_24 | ~spl5_25 | spl5_26 | spl5_27 | ~spl5_18),
% 0.19/0.49    inference(avatar_split_clause,[],[f305,f155,f203,f200,f197,f194])).
% 0.19/0.49  fof(f194,plain,(
% 0.19/0.49    spl5_24 <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.19/0.49  fof(f197,plain,(
% 0.19/0.49    spl5_25 <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.19/0.49  fof(f200,plain,(
% 0.19/0.49    spl5_26 <=> sK3 = k2_mcart_1(k1_mcart_1(sK4))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.19/0.49  fof(f155,plain,(
% 0.19/0.49    spl5_18 <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.19/0.49  fof(f305,plain,(
% 0.19/0.49    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = k2_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)) ) | ~spl5_18),
% 0.19/0.49    inference(superposition,[],[f58,f156])).
% 0.19/0.49  fof(f156,plain,(
% 0.19/0.49    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl5_18),
% 0.19/0.49    inference(avatar_component_clause,[],[f155])).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X6 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f32,f50])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ( ! [X6,X7,X5] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f299,plain,(
% 0.19/0.49    ~spl5_26),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f295])).
% 0.19/0.49  fof(f295,plain,(
% 0.19/0.49    $false | ~spl5_26),
% 0.19/0.49    inference(subsumption_resolution,[],[f115,f201])).
% 0.19/0.49  fof(f201,plain,(
% 0.19/0.49    sK3 = k2_mcart_1(k1_mcart_1(sK4)) | ~spl5_26),
% 0.19/0.49    inference(avatar_component_clause,[],[f200])).
% 0.19/0.49  fof(f115,plain,(
% 0.19/0.49    sK3 != k2_mcart_1(k1_mcart_1(sK4))),
% 0.19/0.49    inference(superposition,[],[f36,f73])).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.19/0.49    inference(global_subsumption,[],[f33,f34,f35,f67])).
% 0.19/0.49  fof(f67,plain,(
% 0.19/0.49    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.19/0.49    inference(resolution,[],[f59,f61])).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.49    inference(definition_unfolding,[],[f55,f51])).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f293,plain,(
% 0.19/0.49    ~spl5_4 | spl5_25),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f292])).
% 0.19/0.49  fof(f292,plain,(
% 0.19/0.49    $false | (~spl5_4 | spl5_25)),
% 0.19/0.49    inference(subsumption_resolution,[],[f285,f263])).
% 0.19/0.49  fof(f263,plain,(
% 0.19/0.49    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | spl5_25),
% 0.19/0.49    inference(resolution,[],[f198,f45])).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.19/0.49  fof(f198,plain,(
% 0.19/0.49    ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | spl5_25),
% 0.19/0.49    inference(avatar_component_clause,[],[f197])).
% 0.19/0.49  fof(f285,plain,(
% 0.19/0.49    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl5_4),
% 0.19/0.49    inference(resolution,[],[f280,f53])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.19/0.49    inference(ennf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.19/0.49  fof(f280,plain,(
% 0.19/0.49    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_4),
% 0.19/0.49    inference(resolution,[],[f88,f52])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f88,plain,(
% 0.19/0.49    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_4),
% 0.19/0.49    inference(avatar_component_clause,[],[f87])).
% 0.19/0.49  fof(f87,plain,(
% 0.19/0.49    spl5_4 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.49  fof(f262,plain,(
% 0.19/0.49    ~spl5_3 | spl5_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f258,f92,f84])).
% 0.19/0.49  fof(f84,plain,(
% 0.19/0.49    spl5_3 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.49  fof(f92,plain,(
% 0.19/0.49    spl5_5 <=> v1_xboole_0(sK4)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.49  fof(f258,plain,(
% 0.19/0.49    v1_xboole_0(sK4) | ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.19/0.49    inference(resolution,[],[f59,f42])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(nnf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.49  fof(f261,plain,(
% 0.19/0.49    spl5_3 | spl5_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f257,f87,f84])).
% 0.19/0.49  fof(f257,plain,(
% 0.19/0.49    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.19/0.49    inference(resolution,[],[f59,f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f28])).
% 0.19/0.49  fof(f260,plain,(
% 0.19/0.49    spl5_1 | spl5_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f259,f80,f77])).
% 0.19/0.49  fof(f259,plain,(
% 0.19/0.49    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.49    inference(global_subsumption,[],[f75])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.49    inference(global_subsumption,[],[f35,f69])).
% 0.19/0.49  fof(f69,plain,(
% 0.19/0.49    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.49    inference(resolution,[],[f59,f49])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.19/0.49    inference(ennf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,axiom,(
% 0.19/0.49    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.19/0.49  fof(f214,plain,(
% 0.19/0.49    ~spl5_4 | spl5_24),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f213])).
% 0.19/0.49  fof(f213,plain,(
% 0.19/0.49    $false | (~spl5_4 | spl5_24)),
% 0.19/0.49    inference(subsumption_resolution,[],[f171,f206])).
% 0.19/0.49  fof(f206,plain,(
% 0.19/0.49    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | spl5_24),
% 0.19/0.49    inference(resolution,[],[f195,f45])).
% 0.19/0.49  fof(f195,plain,(
% 0.19/0.49    ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | spl5_24),
% 0.19/0.49    inference(avatar_component_clause,[],[f194])).
% 0.19/0.49  fof(f171,plain,(
% 0.19/0.49    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl5_4),
% 0.19/0.49    inference(resolution,[],[f167,f52])).
% 0.19/0.49  fof(f167,plain,(
% 0.19/0.49    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_4),
% 0.19/0.49    inference(resolution,[],[f88,f52])).
% 0.19/0.49  fof(f174,plain,(
% 0.19/0.49    ~spl5_17 | spl5_18 | ~spl5_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f173,f87,f155,f152])).
% 0.19/0.49  fof(f152,plain,(
% 0.19/0.49    spl5_17 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.19/0.49  fof(f173,plain,(
% 0.19/0.49    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl5_4),
% 0.19/0.49    inference(resolution,[],[f167,f44])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(flattening,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.19/0.49  fof(f166,plain,(
% 0.19/0.49    ~spl5_2 | ~spl5_5),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f165])).
% 0.19/0.49  fof(f165,plain,(
% 0.19/0.49    $false | (~spl5_2 | ~spl5_5)),
% 0.19/0.49    inference(subsumption_resolution,[],[f96,f93])).
% 0.19/0.49  fof(f93,plain,(
% 0.19/0.49    v1_xboole_0(sK4) | ~spl5_5),
% 0.19/0.49    inference(avatar_component_clause,[],[f92])).
% 0.19/0.49  fof(f96,plain,(
% 0.19/0.49    ~v1_xboole_0(sK4) | ~spl5_2),
% 0.19/0.49    inference(superposition,[],[f37,f81])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v1_xboole_0(k4_tarski(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : ~v1_xboole_0(k4_tarski(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_zfmisc_1)).
% 0.19/0.49  fof(f159,plain,(
% 0.19/0.49    spl5_17),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f158])).
% 0.19/0.49  fof(f158,plain,(
% 0.19/0.49    $false | spl5_17),
% 0.19/0.49    inference(resolution,[],[f153,f38])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.49  fof(f153,plain,(
% 0.19/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl5_17),
% 0.19/0.49    inference(avatar_component_clause,[],[f152])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (13150)------------------------------
% 0.19/0.49  % (13150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (13150)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (13150)Memory used [KB]: 10874
% 0.19/0.49  % (13150)Time elapsed: 0.080 s
% 0.19/0.49  % (13150)------------------------------
% 0.19/0.49  % (13150)------------------------------
% 0.19/0.50  % (13145)Success in time 0.144 s
%------------------------------------------------------------------------------
