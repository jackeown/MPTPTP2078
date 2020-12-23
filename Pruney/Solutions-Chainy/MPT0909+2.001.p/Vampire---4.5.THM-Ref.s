%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:22 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 315 expanded)
%              Number of leaves         :   20 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  369 (1631 expanded)
%              Number of equality atoms :  180 ( 942 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1004,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f775,f782,f847,f897,f985])).

fof(f985,plain,(
    ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f984])).

fof(f984,plain,
    ( $false
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f930,f759])).

fof(f759,plain,
    ( ! [X1] : k1_xboole_0 = X1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f758,f46])).

fof(f46,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X5
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k5_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X5
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X5
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

fof(f758,plain,
    ( ! [X1] :
        ( k1_xboole_0 = X1
        | k1_xboole_0 = sK0 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f757,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f757,plain,
    ( ! [X1] :
        ( k1_xboole_0 = X1
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f756,f48])).

fof(f48,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f756,plain,
    ( ! [X1] :
        ( k1_xboole_0 = X1
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f740,f229])).

fof(f229,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(superposition,[],[f94,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f75,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f69,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f94,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f74,f79])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f740,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
        | k1_xboole_0 = X1
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl9_2 ),
    inference(superposition,[],[f90,f113])).

fof(f113,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl9_2 ),
    inference(resolution,[],[f100,f111])).

fof(f111,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl9_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f100,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f52,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
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

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f71,f79])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f930,plain,
    ( k1_xboole_0 != sK3
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f49,f759])).

fof(f49,plain,(
    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f897,plain,
    ( ~ spl9_1
    | ~ spl9_36 ),
    inference(avatar_contradiction_clause,[],[f896])).

fof(f896,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_36 ),
    inference(subsumption_resolution,[],[f895,f374])).

fof(f374,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl9_1 ),
    inference(resolution,[],[f367,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f367,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl9_1 ),
    inference(resolution,[],[f107,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f107,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl9_1
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f895,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl9_1
    | ~ spl9_36 ),
    inference(trivial_inequality_removal,[],[f894])).

fof(f894,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl9_1
    | ~ spl9_36 ),
    inference(superposition,[],[f716,f372])).

fof(f372,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f369,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f369,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f107,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f716,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f715])).

fof(f715,plain,
    ( spl9_36
  <=> ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | ~ m1_subset_1(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f847,plain,(
    ~ spl9_35 ),
    inference(avatar_contradiction_clause,[],[f846])).

fof(f846,plain,
    ( $false
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f845,f49])).

fof(f845,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK4)
    | ~ spl9_35 ),
    inference(forward_demodulation,[],[f813,f713])).

fof(f713,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f711])).

fof(f711,plain,
    ( spl9_35
  <=> sK3 = k1_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f813,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f812,f46])).

fof(f812,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f811,f47])).

fof(f811,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f802,f48])).

fof(f802,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f84,f81])).

fof(f81,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f44,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f66,f63])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f782,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f778,f109,f105])).

fof(f778,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f81,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f775,plain,
    ( spl9_35
    | spl9_36
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f709,f105,f715,f711])).

fof(f709,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | sK3 = k1_mcart_1(k1_mcart_1(sK4))
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f708,f409])).

fof(f409,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl9_1 ),
    inference(resolution,[],[f385,f58])).

fof(f385,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl9_1 ),
    inference(resolution,[],[f368,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f368,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_1 ),
    inference(resolution,[],[f107,f64])).

fof(f708,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | sK3 = k1_mcart_1(k1_mcart_1(sK4))
        | ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f707,f391])).

fof(f391,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl9_1 ),
    inference(resolution,[],[f384,f58])).

fof(f384,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl9_1 ),
    inference(resolution,[],[f368,f65])).

fof(f707,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | sK3 = k1_mcart_1(k1_mcart_1(sK4))
        | ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) )
    | ~ spl9_1 ),
    inference(superposition,[],[f80,f389])).

fof(f389,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f386,f55])).

fof(f386,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl9_1 ),
    inference(resolution,[],[f368,f56])).

fof(f80,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X5
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f45,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X5
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:31:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (30161)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (30138)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.56  % (30145)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (30153)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (30147)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.57  % (30146)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.57  % (30163)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.57  % (30155)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.57  % (30154)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (30141)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.58  % (30136)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.58  % (30163)Refutation not found, incomplete strategy% (30163)------------------------------
% 0.21/0.58  % (30163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (30154)Refutation not found, incomplete strategy% (30154)------------------------------
% 0.21/0.58  % (30154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (30154)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  % (30163)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (30163)Memory used [KB]: 6268
% 0.21/0.58  % (30163)Time elapsed: 0.156 s
% 0.21/0.58  % (30163)------------------------------
% 0.21/0.58  % (30163)------------------------------
% 0.21/0.58  
% 0.21/0.58  % (30154)Memory used [KB]: 1791
% 0.21/0.58  % (30154)Time elapsed: 0.158 s
% 0.21/0.58  % (30154)------------------------------
% 0.21/0.58  % (30154)------------------------------
% 0.21/0.58  % (30151)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.59  % (30137)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.59  % (30137)Refutation not found, incomplete strategy% (30137)------------------------------
% 0.21/0.59  % (30137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (30137)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (30137)Memory used [KB]: 1663
% 0.21/0.59  % (30137)Time elapsed: 0.133 s
% 0.21/0.59  % (30137)------------------------------
% 0.21/0.59  % (30137)------------------------------
% 0.21/0.59  % (30146)Refutation not found, incomplete strategy% (30146)------------------------------
% 0.21/0.59  % (30146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (30146)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (30146)Memory used [KB]: 10874
% 0.21/0.59  % (30146)Time elapsed: 0.158 s
% 0.21/0.59  % (30146)------------------------------
% 0.21/0.59  % (30146)------------------------------
% 0.21/0.59  % (30142)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.59  % (30165)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.59  % (30165)Refutation not found, incomplete strategy% (30165)------------------------------
% 0.21/0.59  % (30165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (30165)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (30165)Memory used [KB]: 1663
% 0.21/0.59  % (30165)Time elapsed: 0.002 s
% 0.21/0.59  % (30165)------------------------------
% 0.21/0.59  % (30165)------------------------------
% 0.21/0.59  % (30143)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.60  % (30159)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.60  % (30158)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.87/0.61  % (30149)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.87/0.61  % (30157)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.87/0.62  % (30144)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.87/0.62  % (30150)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.87/0.62  % (30150)Refutation not found, incomplete strategy% (30150)------------------------------
% 1.87/0.62  % (30150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (30150)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.62  
% 1.87/0.62  % (30150)Memory used [KB]: 1791
% 1.87/0.62  % (30150)Time elapsed: 0.189 s
% 1.87/0.62  % (30150)------------------------------
% 1.87/0.62  % (30150)------------------------------
% 1.87/0.62  % (30140)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.87/0.62  % (30162)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.87/0.63  % (30152)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 2.06/0.63  % (30152)Refutation not found, incomplete strategy% (30152)------------------------------
% 2.06/0.63  % (30152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.63  % (30152)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.63  
% 2.06/0.63  % (30152)Memory used [KB]: 10618
% 2.06/0.63  % (30152)Time elapsed: 0.198 s
% 2.06/0.63  % (30152)------------------------------
% 2.06/0.63  % (30152)------------------------------
% 2.06/0.63  % (30160)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.06/0.63  % (30160)Refutation not found, incomplete strategy% (30160)------------------------------
% 2.06/0.63  % (30160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.63  % (30160)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.63  
% 2.06/0.63  % (30160)Memory used [KB]: 10746
% 2.06/0.63  % (30160)Time elapsed: 0.208 s
% 2.06/0.63  % (30160)------------------------------
% 2.06/0.63  % (30160)------------------------------
% 2.06/0.64  % (30139)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 2.06/0.64  % (30162)Refutation not found, incomplete strategy% (30162)------------------------------
% 2.06/0.64  % (30162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.64  % (30162)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.64  
% 2.06/0.64  % (30162)Memory used [KB]: 6268
% 2.06/0.64  % (30162)Time elapsed: 0.199 s
% 2.06/0.64  % (30162)------------------------------
% 2.06/0.64  % (30162)------------------------------
% 2.06/0.65  % (30164)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.22/0.65  % (30156)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.22/0.66  % (30148)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.22/0.66  % (30148)Refutation not found, incomplete strategy% (30148)------------------------------
% 2.22/0.66  % (30148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.66  % (30148)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.66  
% 2.22/0.66  % (30148)Memory used [KB]: 10618
% 2.22/0.66  % (30148)Time elapsed: 0.237 s
% 2.22/0.66  % (30148)------------------------------
% 2.22/0.66  % (30148)------------------------------
% 2.22/0.67  % (30142)Refutation found. Thanks to Tanya!
% 2.22/0.67  % SZS status Theorem for theBenchmark
% 2.22/0.67  % SZS output start Proof for theBenchmark
% 2.22/0.67  fof(f1004,plain,(
% 2.22/0.67    $false),
% 2.22/0.67    inference(avatar_sat_refutation,[],[f775,f782,f847,f897,f985])).
% 2.22/0.67  fof(f985,plain,(
% 2.22/0.67    ~spl9_2),
% 2.22/0.67    inference(avatar_contradiction_clause,[],[f984])).
% 2.22/0.67  fof(f984,plain,(
% 2.22/0.67    $false | ~spl9_2),
% 2.22/0.67    inference(subsumption_resolution,[],[f930,f759])).
% 2.22/0.67  fof(f759,plain,(
% 2.22/0.67    ( ! [X1] : (k1_xboole_0 = X1) ) | ~spl9_2),
% 2.22/0.67    inference(subsumption_resolution,[],[f758,f46])).
% 2.22/0.67  fof(f46,plain,(
% 2.22/0.67    k1_xboole_0 != sK0),
% 2.22/0.67    inference(cnf_transformation,[],[f31])).
% 2.22/0.67  fof(f31,plain,(
% 2.22/0.67    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.22/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f30])).
% 2.22/0.67  fof(f30,plain,(
% 2.22/0.67    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 2.22/0.67    introduced(choice_axiom,[])).
% 2.22/0.67  fof(f19,plain,(
% 2.22/0.67    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.22/0.67    inference(flattening,[],[f18])).
% 2.22/0.67  fof(f18,plain,(
% 2.22/0.67    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.22/0.67    inference(ennf_transformation,[],[f17])).
% 2.22/0.67  fof(f17,negated_conjecture,(
% 2.22/0.67    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.22/0.67    inference(negated_conjecture,[],[f16])).
% 2.22/0.67  fof(f16,conjecture,(
% 2.22/0.67    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.22/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).
% 2.22/0.67  fof(f758,plain,(
% 2.22/0.67    ( ! [X1] : (k1_xboole_0 = X1 | k1_xboole_0 = sK0) ) | ~spl9_2),
% 2.22/0.67    inference(subsumption_resolution,[],[f757,f47])).
% 2.22/0.67  fof(f47,plain,(
% 2.22/0.67    k1_xboole_0 != sK1),
% 2.22/0.67    inference(cnf_transformation,[],[f31])).
% 2.22/0.67  fof(f757,plain,(
% 2.22/0.67    ( ! [X1] : (k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl9_2),
% 2.22/0.67    inference(subsumption_resolution,[],[f756,f48])).
% 2.22/0.67  fof(f48,plain,(
% 2.22/0.67    k1_xboole_0 != sK2),
% 2.22/0.67    inference(cnf_transformation,[],[f31])).
% 2.22/0.67  fof(f756,plain,(
% 2.22/0.67    ( ! [X1] : (k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl9_2),
% 2.22/0.67    inference(subsumption_resolution,[],[f740,f229])).
% 2.22/0.67  fof(f229,plain,(
% 2.22/0.67    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 2.22/0.67    inference(superposition,[],[f94,f93])).
% 2.22/0.67  fof(f93,plain,(
% 2.22/0.67    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 2.22/0.67    inference(equality_resolution,[],[f86])).
% 2.22/0.67  fof(f86,plain,(
% 2.22/0.67    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.22/0.67    inference(definition_unfolding,[],[f75,f79])).
% 2.22/0.67  fof(f79,plain,(
% 2.22/0.67    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.22/0.67    inference(definition_unfolding,[],[f69,f63])).
% 2.22/0.67  fof(f63,plain,(
% 2.22/0.67    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f8])).
% 2.22/0.67  fof(f8,axiom,(
% 2.22/0.67    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.22/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.22/0.67  fof(f69,plain,(
% 2.22/0.67    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f9])).
% 2.22/0.67  fof(f9,axiom,(
% 2.22/0.67    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 2.22/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 2.22/0.67  fof(f75,plain,(
% 2.22/0.67    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 2.22/0.67    inference(cnf_transformation,[],[f41])).
% 2.22/0.67  fof(f41,plain,(
% 2.22/0.67    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.22/0.67    inference(flattening,[],[f40])).
% 2.22/0.67  fof(f40,plain,(
% 2.22/0.67    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.22/0.67    inference(nnf_transformation,[],[f15])).
% 2.22/0.67  fof(f15,axiom,(
% 2.22/0.67    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 2.22/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 2.22/0.67  fof(f94,plain,(
% 2.22/0.67    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 2.22/0.67    inference(equality_resolution,[],[f87])).
% 2.22/0.67  fof(f87,plain,(
% 2.22/0.67    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.22/0.67    inference(definition_unfolding,[],[f74,f79])).
% 2.22/0.67  fof(f74,plain,(
% 2.22/0.67    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 2.22/0.67    inference(cnf_transformation,[],[f41])).
% 2.22/0.67  fof(f740,plain,(
% 2.22/0.67    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl9_2),
% 2.22/0.67    inference(superposition,[],[f90,f113])).
% 2.22/0.67  fof(f113,plain,(
% 2.22/0.67    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl9_2),
% 2.22/0.67    inference(resolution,[],[f100,f111])).
% 2.22/0.67  fof(f111,plain,(
% 2.22/0.67    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl9_2),
% 2.22/0.67    inference(avatar_component_clause,[],[f109])).
% 2.22/0.67  fof(f109,plain,(
% 2.22/0.67    spl9_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.22/0.67    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 2.22/0.67  fof(f100,plain,(
% 2.22/0.67    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 2.22/0.67    inference(resolution,[],[f52,f50])).
% 2.22/0.67  fof(f50,plain,(
% 2.22/0.67    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f35])).
% 2.22/0.67  fof(f35,plain,(
% 2.22/0.67    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.22/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 2.22/0.67  fof(f34,plain,(
% 2.22/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 2.22/0.67    introduced(choice_axiom,[])).
% 2.22/0.67  fof(f33,plain,(
% 2.22/0.67    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.22/0.67    inference(rectify,[],[f32])).
% 2.22/0.67  fof(f32,plain,(
% 2.22/0.67    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.22/0.67    inference(nnf_transformation,[],[f1])).
% 2.22/0.67  fof(f1,axiom,(
% 2.22/0.67    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.22/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.22/0.67  fof(f52,plain,(
% 2.22/0.67    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.22/0.67    inference(cnf_transformation,[],[f37])).
% 2.22/0.67  fof(f37,plain,(
% 2.22/0.67    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 2.22/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f36])).
% 2.22/0.68  fof(f36,plain,(
% 2.22/0.68    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f20,plain,(
% 2.22/0.68    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.22/0.68    inference(ennf_transformation,[],[f13])).
% 2.22/0.68  fof(f13,axiom,(
% 2.22/0.68    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 2.22/0.68  fof(f90,plain,(
% 2.22/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.22/0.68    inference(definition_unfolding,[],[f71,f79])).
% 2.22/0.68  fof(f71,plain,(
% 2.22/0.68    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.22/0.68    inference(cnf_transformation,[],[f41])).
% 2.22/0.68  fof(f930,plain,(
% 2.22/0.68    k1_xboole_0 != sK3 | ~spl9_2),
% 2.22/0.68    inference(backward_demodulation,[],[f49,f759])).
% 2.22/0.68  fof(f49,plain,(
% 2.22/0.68    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)),
% 2.22/0.68    inference(cnf_transformation,[],[f31])).
% 2.22/0.68  fof(f897,plain,(
% 2.22/0.68    ~spl9_1 | ~spl9_36),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f896])).
% 2.22/0.68  fof(f896,plain,(
% 2.22/0.68    $false | (~spl9_1 | ~spl9_36)),
% 2.22/0.68    inference(subsumption_resolution,[],[f895,f374])).
% 2.22/0.68  fof(f374,plain,(
% 2.22/0.68    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl9_1),
% 2.22/0.68    inference(resolution,[],[f367,f58])).
% 2.22/0.68  fof(f58,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f25])).
% 2.22/0.68  fof(f25,plain,(
% 2.22/0.68    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.22/0.68    inference(ennf_transformation,[],[f4])).
% 2.22/0.68  fof(f4,axiom,(
% 2.22/0.68    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 2.22/0.68  fof(f367,plain,(
% 2.22/0.68    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl9_1),
% 2.22/0.68    inference(resolution,[],[f107,f65])).
% 2.22/0.68  fof(f65,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f26])).
% 2.22/0.68  fof(f26,plain,(
% 2.22/0.68    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.22/0.68    inference(ennf_transformation,[],[f11])).
% 2.22/0.68  fof(f11,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 2.22/0.68  fof(f107,plain,(
% 2.22/0.68    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl9_1),
% 2.22/0.68    inference(avatar_component_clause,[],[f105])).
% 2.22/0.68  fof(f105,plain,(
% 2.22/0.68    spl9_1 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.22/0.68  fof(f895,plain,(
% 2.22/0.68    ~m1_subset_1(k2_mcart_1(sK4),sK2) | (~spl9_1 | ~spl9_36)),
% 2.22/0.68    inference(trivial_inequality_removal,[],[f894])).
% 2.22/0.68  fof(f894,plain,(
% 2.22/0.68    sK4 != sK4 | ~m1_subset_1(k2_mcart_1(sK4),sK2) | (~spl9_1 | ~spl9_36)),
% 2.22/0.68    inference(superposition,[],[f716,f372])).
% 2.22/0.68  fof(f372,plain,(
% 2.22/0.68    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl9_1),
% 2.22/0.68    inference(subsumption_resolution,[],[f369,f55])).
% 2.22/0.68  fof(f55,plain,(
% 2.22/0.68    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.22/0.68    inference(cnf_transformation,[],[f6])).
% 2.22/0.68  fof(f6,axiom,(
% 2.22/0.68    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.22/0.68  fof(f369,plain,(
% 2.22/0.68    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl9_1),
% 2.22/0.68    inference(resolution,[],[f107,f56])).
% 2.22/0.68  fof(f56,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~v1_relat_1(X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f22])).
% 2.22/0.68  fof(f22,plain,(
% 2.22/0.68    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 2.22/0.68    inference(flattening,[],[f21])).
% 2.22/0.68  fof(f21,plain,(
% 2.22/0.68    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 2.22/0.68    inference(ennf_transformation,[],[f12])).
% 2.22/0.68  fof(f12,axiom,(
% 2.22/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 2.22/0.68  fof(f716,plain,(
% 2.22/0.68    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(X0,sK2)) ) | ~spl9_36),
% 2.22/0.68    inference(avatar_component_clause,[],[f715])).
% 2.22/0.68  fof(f715,plain,(
% 2.22/0.68    spl9_36 <=> ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(X0,sK2))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 2.22/0.68  fof(f847,plain,(
% 2.22/0.68    ~spl9_35),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f846])).
% 2.22/0.68  fof(f846,plain,(
% 2.22/0.68    $false | ~spl9_35),
% 2.22/0.68    inference(subsumption_resolution,[],[f845,f49])).
% 2.22/0.68  fof(f845,plain,(
% 2.22/0.68    sK3 = k5_mcart_1(sK0,sK1,sK2,sK4) | ~spl9_35),
% 2.22/0.68    inference(forward_demodulation,[],[f813,f713])).
% 2.22/0.68  fof(f713,plain,(
% 2.22/0.68    sK3 = k1_mcart_1(k1_mcart_1(sK4)) | ~spl9_35),
% 2.22/0.68    inference(avatar_component_clause,[],[f711])).
% 2.22/0.68  fof(f711,plain,(
% 2.22/0.68    spl9_35 <=> sK3 = k1_mcart_1(k1_mcart_1(sK4))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 2.22/0.68  fof(f813,plain,(
% 2.22/0.68    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 2.22/0.68    inference(subsumption_resolution,[],[f812,f46])).
% 2.22/0.68  fof(f812,plain,(
% 2.22/0.68    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0),
% 2.22/0.68    inference(subsumption_resolution,[],[f811,f47])).
% 2.22/0.68  fof(f811,plain,(
% 2.22/0.68    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 2.22/0.68    inference(subsumption_resolution,[],[f802,f48])).
% 2.22/0.68  fof(f802,plain,(
% 2.22/0.68    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 2.22/0.68    inference(resolution,[],[f84,f81])).
% 2.22/0.68  fof(f81,plain,(
% 2.22/0.68    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.22/0.68    inference(definition_unfolding,[],[f44,f63])).
% 2.22/0.68  fof(f44,plain,(
% 2.22/0.68    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.22/0.68    inference(cnf_transformation,[],[f31])).
% 2.22/0.68  fof(f84,plain,(
% 2.22/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.22/0.68    inference(definition_unfolding,[],[f66,f63])).
% 2.22/0.68  fof(f66,plain,(
% 2.22/0.68    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.22/0.68    inference(cnf_transformation,[],[f27])).
% 2.22/0.68  fof(f27,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.22/0.68    inference(ennf_transformation,[],[f14])).
% 2.22/0.68  fof(f14,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 2.22/0.68  fof(f782,plain,(
% 2.22/0.68    spl9_1 | spl9_2),
% 2.22/0.68    inference(avatar_split_clause,[],[f778,f109,f105])).
% 2.22/0.68  fof(f778,plain,(
% 2.22/0.68    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.22/0.68    inference(resolution,[],[f81,f57])).
% 2.22/0.68  fof(f57,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f24])).
% 2.22/0.68  fof(f24,plain,(
% 2.22/0.68    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.22/0.68    inference(flattening,[],[f23])).
% 2.22/0.68  fof(f23,plain,(
% 2.22/0.68    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.22/0.68    inference(ennf_transformation,[],[f5])).
% 2.22/0.68  fof(f5,axiom,(
% 2.22/0.68    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 2.22/0.68  fof(f775,plain,(
% 2.22/0.68    spl9_35 | spl9_36 | ~spl9_1),
% 2.22/0.68    inference(avatar_split_clause,[],[f709,f105,f715,f711])).
% 2.22/0.68  fof(f709,plain,(
% 2.22/0.68    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = k1_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(X0,sK2)) ) | ~spl9_1),
% 2.22/0.68    inference(subsumption_resolution,[],[f708,f409])).
% 2.22/0.68  fof(f409,plain,(
% 2.22/0.68    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl9_1),
% 2.22/0.68    inference(resolution,[],[f385,f58])).
% 2.22/0.68  fof(f385,plain,(
% 2.22/0.68    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl9_1),
% 2.22/0.68    inference(resolution,[],[f368,f64])).
% 2.22/0.68  fof(f64,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f26])).
% 2.22/0.68  fof(f368,plain,(
% 2.22/0.68    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl9_1),
% 2.22/0.68    inference(resolution,[],[f107,f64])).
% 2.22/0.68  fof(f708,plain,(
% 2.22/0.68    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = k1_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)) ) | ~spl9_1),
% 2.22/0.68    inference(subsumption_resolution,[],[f707,f391])).
% 2.22/0.68  fof(f391,plain,(
% 2.22/0.68    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl9_1),
% 2.22/0.68    inference(resolution,[],[f384,f58])).
% 2.22/0.68  fof(f384,plain,(
% 2.22/0.68    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl9_1),
% 2.22/0.68    inference(resolution,[],[f368,f65])).
% 2.22/0.68  fof(f707,plain,(
% 2.22/0.68    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = k1_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)) ) | ~spl9_1),
% 2.22/0.68    inference(superposition,[],[f80,f389])).
% 2.22/0.68  fof(f389,plain,(
% 2.22/0.68    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl9_1),
% 2.22/0.68    inference(subsumption_resolution,[],[f386,f55])).
% 2.22/0.68  fof(f386,plain,(
% 2.22/0.68    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl9_1),
% 2.22/0.68    inference(resolution,[],[f368,f56])).
% 2.22/0.68  fof(f80,plain,(
% 2.22/0.68    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X5 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 2.22/0.68    inference(definition_unfolding,[],[f45,f62])).
% 2.22/0.68  fof(f62,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f7])).
% 2.22/0.68  fof(f7,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.22/0.68  fof(f45,plain,(
% 2.22/0.68    ( ! [X6,X7,X5] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f31])).
% 2.22/0.68  % SZS output end Proof for theBenchmark
% 2.22/0.68  % (30142)------------------------------
% 2.22/0.68  % (30142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (30142)Termination reason: Refutation
% 2.22/0.68  
% 2.22/0.68  % (30142)Memory used [KB]: 11129
% 2.22/0.68  % (30142)Time elapsed: 0.216 s
% 2.22/0.68  % (30142)------------------------------
% 2.22/0.68  % (30142)------------------------------
% 2.22/0.68  % (30135)Success in time 0.312 s
%------------------------------------------------------------------------------
