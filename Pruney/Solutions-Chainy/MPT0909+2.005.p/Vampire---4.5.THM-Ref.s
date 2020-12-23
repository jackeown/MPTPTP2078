%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:23 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 321 expanded)
%              Number of leaves         :   18 (  84 expanded)
%              Depth                    :   21
%              Number of atoms          :  438 (1953 expanded)
%              Number of equality atoms :  183 ( 989 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f665,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f482,f523,f591,f646,f664])).

fof(f664,plain,(
    ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f663])).

fof(f663,plain,
    ( $false
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f662,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f24])).

fof(f24,plain,
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
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
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

fof(f662,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f661,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f661,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f660,f37])).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f660,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f659,f62])).

fof(f62,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f33,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f659,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f658,f475])).

fof(f475,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f473])).

fof(f473,plain,
    ( spl6_10
  <=> sK3 = k1_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f658,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f38,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f57,f50])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f38,plain,(
    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f646,plain,(
    ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f645])).

fof(f645,plain,
    ( $false
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f644,f35])).

fof(f644,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f643,f36])).

fof(f643,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f642,f37])).

fof(f642,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_12 ),
    inference(trivial_inequality_removal,[],[f637])).

fof(f637,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_12 ),
    inference(superposition,[],[f66,f613])).

fof(f613,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_12 ),
    inference(resolution,[],[f605,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f48,f39])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f605,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_12 ),
    inference(resolution,[],[f598,f62])).

fof(f598,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) )
    | ~ spl6_12 ),
    inference(resolution,[],[f595,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f595,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
    | ~ spl6_12 ),
    inference(resolution,[],[f481,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f481,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl6_12
  <=> ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f50])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f591,plain,(
    ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f590])).

fof(f590,plain,
    ( $false
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f589,f35])).

fof(f589,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f588,f36])).

fof(f588,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f587,f37])).

fof(f587,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_11 ),
    inference(trivial_inequality_removal,[],[f582])).

fof(f582,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_11 ),
    inference(superposition,[],[f66,f558])).

fof(f558,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f550,f74])).

fof(f550,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_11 ),
    inference(resolution,[],[f543,f62])).

fof(f543,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) )
    | ~ spl6_11 ),
    inference(resolution,[],[f540,f43])).

fof(f540,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
    | ~ spl6_11 ),
    inference(resolution,[],[f478,f51])).

fof(f478,plain,
    ( ! [X1] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl6_11
  <=> ! [X1] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f523,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f521,f35])).

fof(f521,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f520,f36])).

fof(f520,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f519,f37])).

fof(f519,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(trivial_inequality_removal,[],[f514])).

fof(f514,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(superposition,[],[f66,f490])).

fof(f490,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_9 ),
    inference(resolution,[],[f485,f74])).

fof(f485,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_9 ),
    inference(resolution,[],[f483,f62])).

fof(f483,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X0,sK2))
        | v1_xboole_0(k2_zfmisc_1(X0,sK2)) )
    | ~ spl6_9 ),
    inference(resolution,[],[f471,f43])).

fof(f471,plain,
    ( ! [X2] : ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl6_9
  <=> ! [X2] : ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f482,plain,
    ( spl6_9
    | spl6_10
    | spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f468,f480,f477,f473,f470])).

fof(f468,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))
      | sK3 = k1_mcart_1(k1_mcart_1(sK4))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2)) ) ),
    inference(equality_resolution,[],[f467])).

fof(f467,plain,(
    ! [X2,X0,X5,X1] :
      ( sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(X0,k2_zfmisc_1(X5,sK2)) ) ),
    inference(condensation,[],[f465])).

fof(f465,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X4))
      | sK4 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X5,sK2)) ) ),
    inference(resolution,[],[f464,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f464,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X3)
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | ~ r2_hidden(X0,X3)
      | sK4 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X6,sK2)) ) ),
    inference(condensation,[],[f462])).

fof(f462,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sK4 != X0
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | ~ r2_hidden(X0,X3)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5))
      | ~ r2_hidden(X0,k2_zfmisc_1(X6,sK2)) ) ),
    inference(resolution,[],[f451,f42])).

fof(f451,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sK4 != X1
      | sK3 = k1_mcart_1(k1_mcart_1(X1))
      | ~ r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(sK0,X3))
      | ~ r2_hidden(X1,X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k1_mcart_1(X1),X0)
      | ~ r2_hidden(X1,k2_zfmisc_1(X5,sK2)) ) ),
    inference(resolution,[],[f428,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f428,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK2)
      | ~ v1_relat_1(X1)
      | sK4 != X0
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3))
      | ~ r2_hidden(X0,X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(resolution,[],[f227,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f44,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
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

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f227,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK2)
      | ~ r2_hidden(k1_mcart_1(X0),X1)
      | ~ v1_relat_1(X1)
      | sK4 != X0
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3))
      | ~ r2_hidden(X0,X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f222,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f222,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK4 != k4_tarski(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X2,sK2)
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,sK1))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,X4)) ) ),
    inference(resolution,[],[f202,f51])).

fof(f202,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),sK0)
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2)
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,sK1)) ) ),
    inference(resolution,[],[f185,f52])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_mcart_1(X1),sK1)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = k1_mcart_1(X1)
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(k1_mcart_1(X1),sK0) ) ),
    inference(resolution,[],[f160,f95])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k2_mcart_1(X0),sK1) ) ),
    inference(resolution,[],[f159,f95])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | k1_mcart_1(X0) = sK3
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f61,f47])).

% (24800)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (24816)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f61,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X5
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f34,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X5
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (24813)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (24805)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (24793)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (24797)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (24791)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (24790)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (24804)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (24803)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (24809)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (24801)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (24812)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (24794)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (24796)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (24815)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (24806)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (24795)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (24817)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (24818)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (24808)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (24807)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (24814)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (24819)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (24810)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (24810)Refutation not found, incomplete strategy% (24810)------------------------------
% 0.21/0.55  % (24810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24810)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24810)Memory used [KB]: 10746
% 0.21/0.55  % (24810)Time elapsed: 0.138 s
% 0.21/0.55  % (24810)------------------------------
% 0.21/0.55  % (24810)------------------------------
% 0.21/0.55  % (24792)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (24802)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (24798)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (24811)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (24812)Refutation not found, incomplete strategy% (24812)------------------------------
% 0.21/0.55  % (24812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24812)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24812)Memory used [KB]: 10874
% 0.21/0.55  % (24812)Time elapsed: 0.155 s
% 0.21/0.55  % (24812)------------------------------
% 0.21/0.55  % (24812)------------------------------
% 1.56/0.56  % (24799)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.56  % (24793)Refutation found. Thanks to Tanya!
% 1.56/0.56  % SZS status Theorem for theBenchmark
% 1.56/0.56  % SZS output start Proof for theBenchmark
% 1.56/0.56  fof(f665,plain,(
% 1.56/0.56    $false),
% 1.56/0.56    inference(avatar_sat_refutation,[],[f482,f523,f591,f646,f664])).
% 1.56/0.56  fof(f664,plain,(
% 1.56/0.56    ~spl6_10),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f663])).
% 1.56/0.56  fof(f663,plain,(
% 1.56/0.56    $false | ~spl6_10),
% 1.56/0.56    inference(subsumption_resolution,[],[f662,f35])).
% 1.56/0.56  fof(f35,plain,(
% 1.56/0.56    k1_xboole_0 != sK0),
% 1.56/0.56    inference(cnf_transformation,[],[f25])).
% 1.56/0.56  fof(f25,plain,(
% 1.56/0.56    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.56/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f24])).
% 1.56/0.56  fof(f24,plain,(
% 1.56/0.56    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.56/0.56    introduced(choice_axiom,[])).
% 1.56/0.56  fof(f16,plain,(
% 1.56/0.56    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.56/0.56    inference(flattening,[],[f15])).
% 1.56/0.56  fof(f15,plain,(
% 1.56/0.56    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.56/0.56    inference(ennf_transformation,[],[f14])).
% 1.56/0.56  fof(f14,negated_conjecture,(
% 1.56/0.56    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.56/0.56    inference(negated_conjecture,[],[f13])).
% 1.56/0.56  fof(f13,conjecture,(
% 1.56/0.56    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).
% 1.56/0.56  fof(f662,plain,(
% 1.56/0.56    k1_xboole_0 = sK0 | ~spl6_10),
% 1.56/0.56    inference(subsumption_resolution,[],[f661,f36])).
% 1.56/0.56  fof(f36,plain,(
% 1.56/0.56    k1_xboole_0 != sK1),
% 1.56/0.56    inference(cnf_transformation,[],[f25])).
% 1.56/0.56  fof(f661,plain,(
% 1.56/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_10),
% 1.56/0.56    inference(subsumption_resolution,[],[f660,f37])).
% 1.56/0.56  fof(f37,plain,(
% 1.56/0.56    k1_xboole_0 != sK2),
% 1.56/0.56    inference(cnf_transformation,[],[f25])).
% 1.56/0.56  fof(f660,plain,(
% 1.56/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_10),
% 1.56/0.56    inference(subsumption_resolution,[],[f659,f62])).
% 1.56/0.56  fof(f62,plain,(
% 1.56/0.56    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.56/0.56    inference(definition_unfolding,[],[f33,f50])).
% 1.56/0.56  fof(f50,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f7])).
% 1.56/0.56  fof(f7,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.56/0.56  fof(f33,plain,(
% 1.56/0.56    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.56/0.56    inference(cnf_transformation,[],[f25])).
% 1.56/0.56  fof(f659,plain,(
% 1.56/0.56    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_10),
% 1.56/0.56    inference(subsumption_resolution,[],[f658,f475])).
% 1.56/0.56  fof(f475,plain,(
% 1.56/0.56    sK3 = k1_mcart_1(k1_mcart_1(sK4)) | ~spl6_10),
% 1.56/0.56    inference(avatar_component_clause,[],[f473])).
% 1.56/0.56  fof(f473,plain,(
% 1.56/0.56    spl6_10 <=> sK3 = k1_mcart_1(k1_mcart_1(sK4))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.56/0.56  fof(f658,plain,(
% 1.56/0.56    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.56/0.56    inference(superposition,[],[f38,f69])).
% 1.56/0.56  fof(f69,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.56/0.56    inference(definition_unfolding,[],[f57,f50])).
% 1.56/0.56  fof(f57,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.56/0.56    inference(cnf_transformation,[],[f22])).
% 1.56/0.56  fof(f22,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.56/0.56    inference(ennf_transformation,[],[f12])).
% 1.56/0.56  fof(f12,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.56/0.56  fof(f38,plain,(
% 1.56/0.56    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)),
% 1.56/0.56    inference(cnf_transformation,[],[f25])).
% 1.56/0.56  fof(f646,plain,(
% 1.56/0.56    ~spl6_12),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f645])).
% 1.56/0.56  fof(f645,plain,(
% 1.56/0.56    $false | ~spl6_12),
% 1.56/0.56    inference(subsumption_resolution,[],[f644,f35])).
% 1.56/0.56  fof(f644,plain,(
% 1.56/0.56    k1_xboole_0 = sK0 | ~spl6_12),
% 1.56/0.56    inference(subsumption_resolution,[],[f643,f36])).
% 1.56/0.56  fof(f643,plain,(
% 1.56/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_12),
% 1.56/0.56    inference(subsumption_resolution,[],[f642,f37])).
% 1.56/0.56  fof(f642,plain,(
% 1.56/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_12),
% 1.56/0.56    inference(trivial_inequality_removal,[],[f637])).
% 1.56/0.56  fof(f637,plain,(
% 1.56/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_12),
% 1.56/0.56    inference(superposition,[],[f66,f613])).
% 1.56/0.56  fof(f613,plain,(
% 1.56/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl6_12),
% 1.56/0.56    inference(resolution,[],[f605,f74])).
% 1.56/0.56  fof(f74,plain,(
% 1.56/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.56/0.56    inference(resolution,[],[f48,f39])).
% 1.56/0.56  fof(f39,plain,(
% 1.56/0.56    v1_xboole_0(k1_xboole_0)),
% 1.56/0.56    inference(cnf_transformation,[],[f2])).
% 1.56/0.56  fof(f2,axiom,(
% 1.56/0.56    v1_xboole_0(k1_xboole_0)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.56/0.56  fof(f48,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f20])).
% 1.56/0.56  fof(f20,plain,(
% 1.56/0.56    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.56/0.56    inference(ennf_transformation,[],[f3])).
% 1.56/0.56  fof(f3,axiom,(
% 1.56/0.56    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.56/0.56  fof(f605,plain,(
% 1.56/0.56    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl6_12),
% 1.56/0.56    inference(resolution,[],[f598,f62])).
% 1.56/0.56  fof(f598,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl6_12),
% 1.56/0.56    inference(resolution,[],[f595,f43])).
% 1.56/0.56  fof(f43,plain,(
% 1.56/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f30])).
% 1.56/0.56  fof(f30,plain,(
% 1.56/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.56/0.56    inference(nnf_transformation,[],[f17])).
% 1.56/0.56  fof(f17,plain,(
% 1.56/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f4])).
% 1.56/0.56  fof(f4,axiom,(
% 1.56/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.56/0.56  fof(f595,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl6_12),
% 1.56/0.56    inference(resolution,[],[f481,f51])).
% 1.56/0.56  fof(f51,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f21])).
% 1.56/0.56  fof(f21,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.56/0.56    inference(ennf_transformation,[],[f9])).
% 1.56/0.56  fof(f9,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.56/0.56  fof(f481,plain,(
% 1.56/0.56    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))) ) | ~spl6_12),
% 1.56/0.56    inference(avatar_component_clause,[],[f480])).
% 1.56/0.56  fof(f480,plain,(
% 1.56/0.56    spl6_12 <=> ! [X0] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.56/0.56  fof(f66,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.56/0.56    inference(definition_unfolding,[],[f53,f50])).
% 1.56/0.56  fof(f53,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.56/0.56    inference(cnf_transformation,[],[f32])).
% 1.56/0.56  fof(f32,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.56/0.56    inference(flattening,[],[f31])).
% 1.56/0.56  fof(f31,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.56/0.56    inference(nnf_transformation,[],[f11])).
% 1.56/0.56  fof(f11,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 1.56/0.56  fof(f591,plain,(
% 1.56/0.56    ~spl6_11),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f590])).
% 1.56/0.56  fof(f590,plain,(
% 1.56/0.56    $false | ~spl6_11),
% 1.56/0.56    inference(subsumption_resolution,[],[f589,f35])).
% 1.56/0.56  fof(f589,plain,(
% 1.56/0.56    k1_xboole_0 = sK0 | ~spl6_11),
% 1.56/0.56    inference(subsumption_resolution,[],[f588,f36])).
% 1.56/0.56  fof(f588,plain,(
% 1.56/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_11),
% 1.56/0.56    inference(subsumption_resolution,[],[f587,f37])).
% 1.56/0.56  fof(f587,plain,(
% 1.56/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_11),
% 1.56/0.56    inference(trivial_inequality_removal,[],[f582])).
% 1.56/0.56  fof(f582,plain,(
% 1.56/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_11),
% 1.56/0.56    inference(superposition,[],[f66,f558])).
% 1.56/0.56  fof(f558,plain,(
% 1.56/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl6_11),
% 1.56/0.56    inference(resolution,[],[f550,f74])).
% 1.56/0.56  fof(f550,plain,(
% 1.56/0.56    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl6_11),
% 1.56/0.56    inference(resolution,[],[f543,f62])).
% 1.56/0.56  fof(f543,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl6_11),
% 1.56/0.56    inference(resolution,[],[f540,f43])).
% 1.56/0.56  fof(f540,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl6_11),
% 1.56/0.56    inference(resolution,[],[f478,f51])).
% 1.56/0.56  fof(f478,plain,(
% 1.56/0.56    ( ! [X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))) ) | ~spl6_11),
% 1.56/0.56    inference(avatar_component_clause,[],[f477])).
% 1.56/0.56  fof(f477,plain,(
% 1.56/0.56    spl6_11 <=> ! [X1] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.56/0.56  fof(f523,plain,(
% 1.56/0.56    ~spl6_9),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f522])).
% 1.56/0.56  fof(f522,plain,(
% 1.56/0.56    $false | ~spl6_9),
% 1.56/0.56    inference(subsumption_resolution,[],[f521,f35])).
% 1.56/0.56  fof(f521,plain,(
% 1.56/0.56    k1_xboole_0 = sK0 | ~spl6_9),
% 1.56/0.56    inference(subsumption_resolution,[],[f520,f36])).
% 1.56/0.56  fof(f520,plain,(
% 1.56/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_9),
% 1.56/0.56    inference(subsumption_resolution,[],[f519,f37])).
% 1.56/0.56  fof(f519,plain,(
% 1.56/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_9),
% 1.56/0.56    inference(trivial_inequality_removal,[],[f514])).
% 1.56/0.56  fof(f514,plain,(
% 1.56/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_9),
% 1.56/0.56    inference(superposition,[],[f66,f490])).
% 1.56/0.56  fof(f490,plain,(
% 1.56/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl6_9),
% 1.56/0.56    inference(resolution,[],[f485,f74])).
% 1.56/0.56  fof(f485,plain,(
% 1.56/0.56    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl6_9),
% 1.56/0.56    inference(resolution,[],[f483,f62])).
% 1.56/0.56  fof(f483,plain,(
% 1.56/0.56    ( ! [X0] : (~m1_subset_1(sK4,k2_zfmisc_1(X0,sK2)) | v1_xboole_0(k2_zfmisc_1(X0,sK2))) ) | ~spl6_9),
% 1.56/0.56    inference(resolution,[],[f471,f43])).
% 1.56/0.56  fof(f471,plain,(
% 1.56/0.56    ( ! [X2] : (~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))) ) | ~spl6_9),
% 1.56/0.56    inference(avatar_component_clause,[],[f470])).
% 1.56/0.56  fof(f470,plain,(
% 1.56/0.56    spl6_9 <=> ! [X2] : ~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.56/0.56  fof(f482,plain,(
% 1.56/0.56    spl6_9 | spl6_10 | spl6_11 | spl6_12),
% 1.56/0.56    inference(avatar_split_clause,[],[f468,f480,f477,f473,f470])).
% 1.56/0.56  fof(f468,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1)) | sK3 = k1_mcart_1(k1_mcart_1(sK4)) | ~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))) )),
% 1.56/0.56    inference(equality_resolution,[],[f467])).
% 1.56/0.56  fof(f467,plain,(
% 1.56/0.56    ( ! [X2,X0,X5,X1] : (sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(X0,k2_zfmisc_1(X5,sK2))) )),
% 1.56/0.56    inference(condensation,[],[f465])).
% 1.56/0.56  fof(f465,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X0,k2_zfmisc_1(X3,X4)) | sK4 != X0 | ~r2_hidden(X0,k2_zfmisc_1(X5,sK2))) )),
% 1.56/0.56    inference(resolution,[],[f464,f42])).
% 1.56/0.56  fof(f42,plain,(
% 1.56/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f5])).
% 1.56/0.56  fof(f5,axiom,(
% 1.56/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.56/0.56  fof(f464,plain,(
% 1.56/0.56    ( ! [X6,X2,X0,X3,X1] : (~v1_relat_1(X3) | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X0,X3) | sK4 != X0 | ~r2_hidden(X0,k2_zfmisc_1(X6,sK2))) )),
% 1.56/0.56    inference(condensation,[],[f462])).
% 1.56/0.56  fof(f462,plain,(
% 1.56/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sK4 != X0 | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X0,X3) | ~v1_relat_1(X3) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5)) | ~r2_hidden(X0,k2_zfmisc_1(X6,sK2))) )),
% 1.56/0.56    inference(resolution,[],[f451,f42])).
% 1.56/0.56  fof(f451,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_relat_1(X0) | sK4 != X1 | sK3 = k1_mcart_1(k1_mcart_1(X1)) | ~r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK1)) | ~r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(sK0,X3)) | ~r2_hidden(X1,X4) | ~v1_relat_1(X4) | ~r2_hidden(k1_mcart_1(X1),X0) | ~r2_hidden(X1,k2_zfmisc_1(X5,sK2))) )),
% 1.56/0.56    inference(resolution,[],[f428,f52])).
% 1.56/0.56  fof(f52,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f21])).
% 1.56/0.56  fof(f428,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK2) | ~v1_relat_1(X1) | sK4 != X0 | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3)) | ~r2_hidden(X0,X4) | ~v1_relat_1(X4) | ~r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.56/0.56    inference(resolution,[],[f227,f95])).
% 1.56/0.56  fof(f95,plain,(
% 1.56/0.56    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.56/0.56    inference(subsumption_resolution,[],[f44,f40])).
% 1.56/0.56  fof(f40,plain,(
% 1.56/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f29])).
% 1.56/0.56  fof(f29,plain,(
% 1.56/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.56/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 1.56/0.56  fof(f28,plain,(
% 1.56/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.56/0.56    introduced(choice_axiom,[])).
% 1.56/0.56  fof(f27,plain,(
% 1.56/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.56/0.56    inference(rectify,[],[f26])).
% 1.56/0.56  fof(f26,plain,(
% 1.56/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.56/0.56    inference(nnf_transformation,[],[f1])).
% 1.56/0.56  fof(f1,axiom,(
% 1.56/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.56/0.56  fof(f44,plain,(
% 1.56/0.56    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f30])).
% 1.56/0.56  fof(f227,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK2) | ~r2_hidden(k1_mcart_1(X0),X1) | ~v1_relat_1(X1) | sK4 != X0 | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3)) | ~r2_hidden(X0,X4) | ~v1_relat_1(X4)) )),
% 1.56/0.56    inference(superposition,[],[f222,f47])).
% 1.56/0.56  fof(f47,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f19])).
% 1.56/0.56  fof(f19,plain,(
% 1.56/0.56    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.56/0.56    inference(flattening,[],[f18])).
% 1.56/0.56  fof(f18,plain,(
% 1.56/0.56    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.56/0.56    inference(ennf_transformation,[],[f10])).
% 1.56/0.56  fof(f10,axiom,(
% 1.56/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.56/0.56  fof(f222,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X3,X1] : (sK4 != k4_tarski(X0,X2) | ~r2_hidden(X0,X1) | ~v1_relat_1(X1) | ~m1_subset_1(X2,sK2) | k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X3,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,X4))) )),
% 1.56/0.56    inference(resolution,[],[f202,f51])).
% 1.56/0.56  fof(f202,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(X0),sK0) | k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2) | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~r2_hidden(X0,k2_zfmisc_1(X3,sK1))) )),
% 1.56/0.56    inference(resolution,[],[f185,f52])).
% 1.56/0.56  fof(f185,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k2_mcart_1(X1),sK1) | sK4 != k4_tarski(X1,X0) | sK3 = k1_mcart_1(X1) | ~r2_hidden(X1,X2) | ~v1_relat_1(X2) | ~m1_subset_1(X0,sK2) | ~r2_hidden(k1_mcart_1(X1),sK0)) )),
% 1.56/0.56    inference(resolution,[],[f160,f95])).
% 1.56/0.56  fof(f160,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(k1_mcart_1(X0),sK0) | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2) | ~r2_hidden(k2_mcart_1(X0),sK1)) )),
% 1.56/0.56    inference(resolution,[],[f159,f95])).
% 1.56/0.56  fof(f159,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | k1_mcart_1(X0) = sK3 | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(k1_mcart_1(X0),sK0) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 1.56/0.56    inference(superposition,[],[f61,f47])).
% 1.56/0.57  % (24800)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.56/0.57  % (24816)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.69/0.58  fof(f61,plain,(
% 1.69/0.58    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X5 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.69/0.58    inference(definition_unfolding,[],[f34,f49])).
% 1.69/0.58  fof(f49,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f6])).
% 1.69/0.58  fof(f6,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.69/0.58  fof(f34,plain,(
% 1.69/0.58    ( ! [X6,X7,X5] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f25])).
% 1.69/0.58  % SZS output end Proof for theBenchmark
% 1.69/0.58  % (24793)------------------------------
% 1.69/0.58  % (24793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (24793)Termination reason: Refutation
% 1.69/0.58  
% 1.69/0.58  % (24793)Memory used [KB]: 11001
% 1.69/0.58  % (24793)Time elapsed: 0.143 s
% 1.69/0.58  % (24793)------------------------------
% 1.69/0.58  % (24793)------------------------------
% 1.69/0.59  % (24789)Success in time 0.23 s
%------------------------------------------------------------------------------
