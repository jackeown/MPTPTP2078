%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 618 expanded)
%              Number of leaves         :   20 ( 205 expanded)
%              Depth                    :   18
%              Number of atoms          :  376 (2442 expanded)
%              Number of equality atoms :  235 (1857 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f536,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f157,f212,f531])).

fof(f531,plain,(
    ! [X0] :
      ( ~ sP0(sK7,X0)
      | ~ r2_hidden(sK7,X0) ) ),
    inference(subsumption_resolution,[],[f529,f212])).

fof(f529,plain,(
    ! [X0] :
      ( ~ sP0(sK7,k1_enumset1(sK7,sK7,sK7))
      | ~ sP0(sK7,X0)
      | ~ r2_hidden(sK7,X0) ) ),
    inference(superposition,[],[f360,f425])).

fof(f425,plain,(
    ! [X0] :
      ( sK7 = k1_mcart_1(k1_mcart_1(sK7))
      | ~ sP0(sK7,X0)
      | ~ r2_hidden(sK7,X0) ) ),
    inference(superposition,[],[f396,f269])).

fof(f269,plain,
    ( sK7 = k2_mcart_1(k1_mcart_1(sK7))
    | sK7 = k1_mcart_1(k1_mcart_1(sK7)) ),
    inference(subsumption_resolution,[],[f266,f188])).

fof(f188,plain,(
    sP1(sK7,sK6,sK5,sK4) ),
    inference(subsumption_resolution,[],[f187,f52])).

fof(f52,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( sK7 = k7_mcart_1(sK4,sK5,sK6,sK7)
      | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7)
      | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7) )
    & m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f18,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK4,sK5,sK6,X3) = X3
            | k6_mcart_1(sK4,sK5,sK6,X3) = X3
            | k5_mcart_1(sK4,sK5,sK6,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK4,sK5,sK6)) )
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK4,sK5,sK6,X3) = X3
          | k6_mcart_1(sK4,sK5,sK6,X3) = X3
          | k5_mcart_1(sK4,sK5,sK6,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK4,sK5,sK6)) )
   => ( ( sK7 = k7_mcart_1(sK4,sK5,sK6,sK7)
        | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7)
        | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7) )
      & m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f187,plain,
    ( sP1(sK7,sK6,sK5,sK4)
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f186,f53])).

fof(f53,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f33])).

fof(f186,plain,
    ( sP1(sK7,sK6,sK5,sK4)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f185,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f33])).

fof(f185,plain,
    ( sP1(sK7,sK6,sK5,sK4)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f105,f94])).

fof(f94,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f55,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f55,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f33])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sP1(X3,X2,X1,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f82,f74])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X3,X2,X1,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP1(X3,X2,X1,X0)
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f22,f26])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP1(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f266,plain,
    ( sK7 = k1_mcart_1(k1_mcart_1(sK7))
    | sK7 = k2_mcart_1(k1_mcart_1(sK7))
    | ~ sP1(sK7,sK6,sK5,sK4) ),
    inference(superposition,[],[f259,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
        & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
        & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP1(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f259,plain,
    ( sK7 = k5_mcart_1(sK4,sK5,sK6,sK7)
    | sK7 = k2_mcart_1(k1_mcart_1(sK7)) ),
    inference(subsumption_resolution,[],[f256,f188])).

fof(f256,plain,
    ( sK7 = k2_mcart_1(k1_mcart_1(sK7))
    | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7)
    | ~ sP1(sK7,sK6,sK5,sK4) ),
    inference(superposition,[],[f208,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f208,plain,
    ( sK7 = k6_mcart_1(sK4,sK5,sK6,sK7)
    | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(subsumption_resolution,[],[f207,f52])).

fof(f207,plain,
    ( k1_xboole_0 = sK4
    | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7)
    | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(subsumption_resolution,[],[f206,f53])).

fof(f206,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7)
    | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(subsumption_resolution,[],[f205,f54])).

fof(f205,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7)
    | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(subsumption_resolution,[],[f204,f94])).

fof(f204,plain,
    ( ~ m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7)
    | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(subsumption_resolution,[],[f192,f115])).

fof(f115,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(forward_demodulation,[],[f106,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f106,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f192,plain,
    ( sK7 = k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),sK7)
    | ~ m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7)
    | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(superposition,[],[f104,f56])).

fof(f56,plain,
    ( sK7 = k7_mcart_1(sK4,sK5,sK6,sK7)
    | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7)
    | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f78,f73,f74])).

fof(f73,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f396,plain,(
    ! [X1] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X1)
      | ~ sP0(sK7,X1) ) ),
    inference(subsumption_resolution,[],[f395,f188])).

fof(f395,plain,(
    ! [X1] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X1)
      | ~ sP0(sK7,X1)
      | ~ sP1(sK7,sK6,sK5,sK4) ) ),
    inference(superposition,[],[f347,f80])).

fof(f347,plain,(
    ! [X0] :
      ( ~ r2_hidden(k6_mcart_1(sK4,sK5,sK6,sK7),X0)
      | ~ sP0(sK7,X0) ) ),
    inference(subsumption_resolution,[],[f346,f52])).

fof(f346,plain,(
    ! [X0] :
      ( ~ r2_hidden(k6_mcart_1(sK4,sK5,sK6,sK7),X0)
      | ~ sP0(sK7,X0)
      | k1_xboole_0 = sK4 ) ),
    inference(subsumption_resolution,[],[f345,f53])).

fof(f345,plain,(
    ! [X0] :
      ( ~ r2_hidden(k6_mcart_1(sK4,sK5,sK6,sK7),X0)
      | ~ sP0(sK7,X0)
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4 ) ),
    inference(subsumption_resolution,[],[f344,f54])).

fof(f344,plain,(
    ! [X0] :
      ( ~ r2_hidden(k6_mcart_1(sK4,sK5,sK6,sK7),X0)
      | ~ sP0(sK7,X0)
      | k1_xboole_0 = sK6
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4 ) ),
    inference(resolution,[],[f194,f94])).

fof(f194,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(X8,k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7))
      | ~ r2_hidden(k6_mcart_1(X5,X6,X7,X8),X9)
      | ~ sP0(X8,X9)
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5 ) ),
    inference(superposition,[],[f108,f104])).

fof(f108,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ sP0(k4_tarski(k4_tarski(X2,X3),X4),X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != X0
      | ~ r2_hidden(X3,X1)
      | ~ sP0(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f73])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_mcart_1(X2,X3,X4) != X0
      | ~ r2_hidden(X3,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X0
          | ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X1) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f360,plain,(
    ~ sP0(sK7,k1_enumset1(k1_mcart_1(k1_mcart_1(sK7)),k1_mcart_1(k1_mcart_1(sK7)),k1_mcart_1(k1_mcart_1(sK7)))) ),
    inference(resolution,[],[f353,f157])).

fof(f353,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X1)
      | ~ sP0(sK7,X1) ) ),
    inference(subsumption_resolution,[],[f352,f188])).

fof(f352,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X1)
      | ~ sP0(sK7,X1)
      | ~ sP1(sK7,sK6,sK5,sK4) ) ),
    inference(superposition,[],[f343,f79])).

fof(f343,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_mcart_1(sK4,sK5,sK6,sK7),X0)
      | ~ sP0(sK7,X0) ) ),
    inference(subsumption_resolution,[],[f342,f52])).

fof(f342,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_mcart_1(sK4,sK5,sK6,sK7),X0)
      | ~ sP0(sK7,X0)
      | k1_xboole_0 = sK4 ) ),
    inference(subsumption_resolution,[],[f341,f53])).

fof(f341,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_mcart_1(sK4,sK5,sK6,sK7),X0)
      | ~ sP0(sK7,X0)
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4 ) ),
    inference(subsumption_resolution,[],[f340,f54])).

fof(f340,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_mcart_1(sK4,sK5,sK6,sK7),X0)
      | ~ sP0(sK7,X0)
      | k1_xboole_0 = sK6
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4 ) ),
    inference(resolution,[],[f193,f94])).

fof(f193,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X3),X4)
      | ~ sP0(X3,X4)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f109,f104])).

fof(f109,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ sP0(k4_tarski(k4_tarski(X2,X3),X4),X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != X0
      | ~ r2_hidden(X2,X1)
      | ~ sP0(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f73])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_mcart_1(X2,X3,X4) != X0
      | ~ r2_hidden(X2,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f212,plain,(
    ! [X0] : sP0(X0,k1_enumset1(X0,X0,X0)) ),
    inference(subsumption_resolution,[],[f210,f128])).

fof(f128,plain,(
    ! [X0,X1] : k1_xboole_0 != k1_enumset1(X0,X0,X1) ),
    inference(subsumption_resolution,[],[f126,f123])).

fof(f123,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f121])).

fof(f121,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f98,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f98,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f69,f93])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f126,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_enumset1(X0,X0,X1)
      | r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f102,f58])).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f76,f66])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f210,plain,(
    ! [X0] :
      ( sP0(X0,k1_enumset1(X0,X0,X0))
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f65,f184])).

fof(f184,plain,(
    ! [X0] : sK8(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(subsumption_resolution,[],[f180,f128])).

fof(f180,plain,(
    ! [X0] :
      ( sK8(k1_enumset1(X0,X0,X0)) = X0
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(resolution,[],[f167,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( sP0(sK8(X0),X0)
        & r2_hidden(sK8(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK8(X0),X0)
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f20,f24])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f167,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k1_enumset1(X7,X7,X7))
      | X7 = X8 ) ),
    inference(trivial_inequality_removal,[],[f166])).

fof(f166,plain,(
    ! [X8,X7] :
      ( k1_enumset1(X7,X7,X7) != k1_enumset1(X7,X7,X7)
      | ~ r2_hidden(X8,k1_enumset1(X7,X7,X7))
      | X7 = X8 ) ),
    inference(superposition,[],[f98,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f72,f93,f93,f93])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f65,plain,(
    ! [X0] :
      ( sP0(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f157,plain,(
    ! [X1] : r2_hidden(X1,k1_enumset1(X1,X1,X1)) ),
    inference(trivial_inequality_removal,[],[f156])).

fof(f156,plain,(
    ! [X1] :
      ( k1_enumset1(X1,X1,X1) != k1_enumset1(X1,X1,X1)
      | r2_hidden(X1,k1_enumset1(X1,X1,X1)) ) ),
    inference(superposition,[],[f110,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f70,f93])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,(
    ! [X1] : k1_enumset1(X1,X1,X1) != k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f71,f93,f93,f93])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:42:18 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (10801)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (10824)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (10809)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (10821)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (10798)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (10813)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (10804)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (10795)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (10805)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (10805)Refutation not found, incomplete strategy% (10805)------------------------------
% 0.21/0.53  % (10805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10805)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10805)Memory used [KB]: 10746
% 0.21/0.53  % (10805)Time elapsed: 0.125 s
% 0.21/0.53  % (10805)------------------------------
% 0.21/0.53  % (10805)------------------------------
% 0.21/0.54  % (10796)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (10797)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (10799)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (10806)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (10803)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (10797)Refutation not found, incomplete strategy% (10797)------------------------------
% 0.21/0.54  % (10797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10797)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10797)Memory used [KB]: 10746
% 0.21/0.54  % (10797)Time elapsed: 0.124 s
% 0.21/0.54  % (10797)------------------------------
% 0.21/0.54  % (10797)------------------------------
% 0.21/0.54  % (10803)Refutation not found, incomplete strategy% (10803)------------------------------
% 0.21/0.54  % (10803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10803)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10803)Memory used [KB]: 10746
% 0.21/0.54  % (10803)Time elapsed: 0.123 s
% 0.21/0.54  % (10803)------------------------------
% 0.21/0.54  % (10803)------------------------------
% 0.21/0.54  % (10820)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (10806)Refutation not found, incomplete strategy% (10806)------------------------------
% 0.21/0.54  % (10806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10806)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10806)Memory used [KB]: 10618
% 0.21/0.55  % (10806)Time elapsed: 0.112 s
% 0.21/0.55  % (10806)------------------------------
% 0.21/0.55  % (10806)------------------------------
% 0.21/0.55  % (10815)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (10819)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (10800)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (10804)Refutation not found, incomplete strategy% (10804)------------------------------
% 0.21/0.55  % (10804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10804)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10804)Memory used [KB]: 10746
% 0.21/0.55  % (10804)Time elapsed: 0.113 s
% 0.21/0.55  % (10804)------------------------------
% 0.21/0.55  % (10804)------------------------------
% 0.21/0.55  % (10802)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (10795)Refutation not found, incomplete strategy% (10795)------------------------------
% 0.21/0.55  % (10795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10795)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10795)Memory used [KB]: 1791
% 0.21/0.55  % (10795)Time elapsed: 0.144 s
% 0.21/0.55  % (10795)------------------------------
% 0.21/0.55  % (10795)------------------------------
% 0.21/0.55  % (10817)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (10807)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (10812)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (10818)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (10812)Refutation not found, incomplete strategy% (10812)------------------------------
% 0.21/0.56  % (10812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10812)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10812)Memory used [KB]: 10618
% 0.21/0.56  % (10812)Time elapsed: 0.149 s
% 0.21/0.56  % (10812)------------------------------
% 0.21/0.56  % (10812)------------------------------
% 0.21/0.56  % (10823)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (10816)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (10818)Refutation not found, incomplete strategy% (10818)------------------------------
% 0.21/0.56  % (10818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10818)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10818)Memory used [KB]: 1791
% 0.21/0.56  % (10818)Time elapsed: 0.110 s
% 0.21/0.56  % (10818)------------------------------
% 0.21/0.56  % (10818)------------------------------
% 0.21/0.56  % (10824)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f536,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f157,f212,f531])).
% 0.21/0.56  fof(f531,plain,(
% 0.21/0.56    ( ! [X0] : (~sP0(sK7,X0) | ~r2_hidden(sK7,X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f529,f212])).
% 0.21/0.56  fof(f529,plain,(
% 0.21/0.56    ( ! [X0] : (~sP0(sK7,k1_enumset1(sK7,sK7,sK7)) | ~sP0(sK7,X0) | ~r2_hidden(sK7,X0)) )),
% 0.21/0.56    inference(superposition,[],[f360,f425])).
% 0.21/0.56  fof(f425,plain,(
% 0.21/0.56    ( ! [X0] : (sK7 = k1_mcart_1(k1_mcart_1(sK7)) | ~sP0(sK7,X0) | ~r2_hidden(sK7,X0)) )),
% 0.21/0.56    inference(superposition,[],[f396,f269])).
% 0.21/0.56  fof(f269,plain,(
% 0.21/0.56    sK7 = k2_mcart_1(k1_mcart_1(sK7)) | sK7 = k1_mcart_1(k1_mcart_1(sK7))),
% 0.21/0.56    inference(subsumption_resolution,[],[f266,f188])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    sP1(sK7,sK6,sK5,sK4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f187,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    k1_xboole_0 != sK4),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ((sK7 = k7_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6))) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f18,f32,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK4,sK5,sK6,X3) = X3 | k6_mcart_1(sK4,sK5,sK6,X3) = X3 | k5_mcart_1(sK4,sK5,sK6,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK4,sK5,sK6))) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4)),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ? [X3] : ((k7_mcart_1(sK4,sK5,sK6,X3) = X3 | k6_mcart_1(sK4,sK5,sK6,X3) = X3 | k5_mcart_1(sK4,sK5,sK6,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK4,sK5,sK6))) => ((sK7 = k7_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.56    inference(negated_conjecture,[],[f16])).
% 0.21/0.56  fof(f16,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 0.21/0.56  fof(f187,plain,(
% 0.21/0.56    sP1(sK7,sK6,sK5,sK4) | k1_xboole_0 = sK4),
% 0.21/0.56    inference(subsumption_resolution,[],[f186,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    k1_xboole_0 != sK5),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f186,plain,(
% 0.21/0.56    sP1(sK7,sK6,sK5,sK4) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.21/0.56    inference(subsumption_resolution,[],[f185,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    k1_xboole_0 != sK6),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f185,plain,(
% 0.21/0.56    sP1(sK7,sK6,sK5,sK4) | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.21/0.56    inference(resolution,[],[f105,f94])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 0.21/0.56    inference(definition_unfolding,[],[f55,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sP1(X3,X2,X1,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f82,f74])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (sP1(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (! [X3] : (sP1(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.56    inference(definition_folding,[],[f22,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP1(X3,X2,X1,X0))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.56  fof(f266,plain,(
% 0.21/0.56    sK7 = k1_mcart_1(k1_mcart_1(sK7)) | sK7 = k2_mcart_1(k1_mcart_1(sK7)) | ~sP1(sK7,sK6,sK5,sK4)),
% 0.21/0.56    inference(superposition,[],[f259,f79])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))) | ~sP1(X0,X1,X2,X3))),
% 0.21/0.56    inference(rectify,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP1(X3,X2,X1,X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f26])).
% 0.21/0.56  fof(f259,plain,(
% 0.21/0.56    sK7 = k5_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k2_mcart_1(k1_mcart_1(sK7))),
% 0.21/0.56    inference(subsumption_resolution,[],[f256,f188])).
% 0.21/0.56  fof(f256,plain,(
% 0.21/0.56    sK7 = k2_mcart_1(k1_mcart_1(sK7)) | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7) | ~sP1(sK7,sK6,sK5,sK4)),
% 0.21/0.56    inference(superposition,[],[f208,f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f43])).
% 0.21/0.56  fof(f208,plain,(
% 0.21/0.56    sK7 = k6_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.56    inference(subsumption_resolution,[],[f207,f52])).
% 0.21/0.56  fof(f207,plain,(
% 0.21/0.56    k1_xboole_0 = sK4 | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.56    inference(subsumption_resolution,[],[f206,f53])).
% 0.21/0.56  fof(f206,plain,(
% 0.21/0.56    k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.56    inference(subsumption_resolution,[],[f205,f54])).
% 0.21/0.56  fof(f205,plain,(
% 0.21/0.56    k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.56    inference(subsumption_resolution,[],[f204,f94])).
% 0.21/0.56  fof(f204,plain,(
% 0.21/0.56    ~m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.56    inference(subsumption_resolution,[],[f192,f115])).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 0.21/0.56    inference(forward_demodulation,[],[f106,f68])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.56    inference(equality_resolution,[],[f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.56  fof(f192,plain,(
% 0.21/0.56    sK7 = k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),sK7) | ~m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.56    inference(superposition,[],[f104,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    sK7 = k7_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k6_mcart_1(sK4,sK5,sK6,sK7) | sK7 = k5_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f78,f73,f74])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.21/0.56  fof(f396,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X1) | ~sP0(sK7,X1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f395,f188])).
% 0.21/0.56  fof(f395,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X1) | ~sP0(sK7,X1) | ~sP1(sK7,sK6,sK5,sK4)) )),
% 0.21/0.56    inference(superposition,[],[f347,f80])).
% 0.21/0.56  fof(f347,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k6_mcart_1(sK4,sK5,sK6,sK7),X0) | ~sP0(sK7,X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f346,f52])).
% 0.21/0.56  fof(f346,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k6_mcart_1(sK4,sK5,sK6,sK7),X0) | ~sP0(sK7,X0) | k1_xboole_0 = sK4) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f345,f53])).
% 0.21/0.56  fof(f345,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k6_mcart_1(sK4,sK5,sK6,sK7),X0) | ~sP0(sK7,X0) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f344,f54])).
% 0.21/0.56  fof(f344,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k6_mcart_1(sK4,sK5,sK6,sK7),X0) | ~sP0(sK7,X0) | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4) )),
% 0.21/0.56    inference(resolution,[],[f194,f94])).
% 0.21/0.56  fof(f194,plain,(
% 0.21/0.56    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(X8,k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7)) | ~r2_hidden(k6_mcart_1(X5,X6,X7,X8),X9) | ~sP0(X8,X9) | k1_xboole_0 = X7 | k1_xboole_0 = X6 | k1_xboole_0 = X5) )),
% 0.21/0.56    inference(superposition,[],[f108,f104])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    ( ! [X4,X2,X3,X1] : (~sP0(k4_tarski(k4_tarski(X2,X3),X4),X1) | ~r2_hidden(X3,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(X2,X3),X4) != X0 | ~r2_hidden(X3,X1) | ~sP0(X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f63,f73])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_mcart_1(X2,X3,X4) != X0 | ~r2_hidden(X3,X1) | ~sP0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X0 | (~r2_hidden(X3,X1) & ~r2_hidden(X2,X1))) | ~sP0(X0,X1))),
% 0.21/0.56    inference(rectify,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X1,X0] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X1,X0] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.56  fof(f360,plain,(
% 0.21/0.56    ~sP0(sK7,k1_enumset1(k1_mcart_1(k1_mcart_1(sK7)),k1_mcart_1(k1_mcart_1(sK7)),k1_mcart_1(k1_mcart_1(sK7))))),
% 0.21/0.56    inference(resolution,[],[f353,f157])).
% 0.21/0.56  fof(f353,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X1) | ~sP0(sK7,X1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f352,f188])).
% 0.21/0.56  fof(f352,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X1) | ~sP0(sK7,X1) | ~sP1(sK7,sK6,sK5,sK4)) )),
% 0.21/0.56    inference(superposition,[],[f343,f79])).
% 0.21/0.56  fof(f343,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k5_mcart_1(sK4,sK5,sK6,sK7),X0) | ~sP0(sK7,X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f342,f52])).
% 0.21/0.56  fof(f342,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k5_mcart_1(sK4,sK5,sK6,sK7),X0) | ~sP0(sK7,X0) | k1_xboole_0 = sK4) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f341,f53])).
% 0.21/0.56  fof(f341,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k5_mcart_1(sK4,sK5,sK6,sK7),X0) | ~sP0(sK7,X0) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f340,f54])).
% 0.21/0.56  fof(f340,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k5_mcart_1(sK4,sK5,sK6,sK7),X0) | ~sP0(sK7,X0) | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4) )),
% 0.21/0.56    inference(resolution,[],[f193,f94])).
% 0.21/0.56  fof(f193,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X3),X4) | ~sP0(X3,X4) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(superposition,[],[f109,f104])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ( ! [X4,X2,X3,X1] : (~sP0(k4_tarski(k4_tarski(X2,X3),X4),X1) | ~r2_hidden(X2,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f96])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(X2,X3),X4) != X0 | ~r2_hidden(X2,X1) | ~sP0(X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f62,f73])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_mcart_1(X2,X3,X4) != X0 | ~r2_hidden(X2,X1) | ~sP0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f212,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(X0,k1_enumset1(X0,X0,X0))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f210,f128])).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_xboole_0 != k1_enumset1(X0,X0,X1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f126,f123])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f121])).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(superposition,[],[f98,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f69,f93])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f59,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.56  fof(f126,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_xboole_0 != k1_enumset1(X0,X0,X1) | r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.56    inference(superposition,[],[f102,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f76,f66])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.56    inference(flattening,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.56    inference(nnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 0.21/0.56  fof(f210,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(X0,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.56    inference(superposition,[],[f65,f184])).
% 0.21/0.56  fof(f184,plain,(
% 0.21/0.56    ( ! [X0] : (sK8(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f180,f128])).
% 0.21/0.56  fof(f180,plain,(
% 0.21/0.56    ( ! [X0] : (sK8(k1_enumset1(X0,X0,X0)) = X0 | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.56    inference(resolution,[],[f167,f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0] : ((sP0(sK8(X0),X0) & r2_hidden(sK8(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK8(X0),X0) & r2_hidden(sK8(X0),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(definition_folding,[],[f20,f24])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    ( ! [X8,X7] : (~r2_hidden(X8,k1_enumset1(X7,X7,X7)) | X7 = X8) )),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f166])).
% 0.21/0.56  fof(f166,plain,(
% 0.21/0.56    ( ! [X8,X7] : (k1_enumset1(X7,X7,X7) != k1_enumset1(X7,X7,X7) | ~r2_hidden(X8,k1_enumset1(X7,X7,X7)) | X7 = X8) )),
% 0.21/0.56    inference(superposition,[],[f98,f99])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 = X1) )),
% 0.21/0.56    inference(definition_unfolding,[],[f72,f93,f93,f93])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.56    inference(nnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f157,plain,(
% 0.21/0.56    ( ! [X1] : (r2_hidden(X1,k1_enumset1(X1,X1,X1))) )),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f156])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    ( ! [X1] : (k1_enumset1(X1,X1,X1) != k1_enumset1(X1,X1,X1) | r2_hidden(X1,k1_enumset1(X1,X1,X1))) )),
% 0.21/0.56    inference(superposition,[],[f110,f97])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f70,f93])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    ( ! [X1] : (k1_enumset1(X1,X1,X1) != k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f100])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    ( ! [X0,X1] : (X0 != X1 | k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f71,f93,f93,f93])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (10824)------------------------------
% 0.21/0.56  % (10824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10824)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (10824)Memory used [KB]: 2046
% 0.21/0.56  % (10824)Time elapsed: 0.139 s
% 0.21/0.56  % (10824)------------------------------
% 0.21/0.56  % (10824)------------------------------
% 0.21/0.56  % (10794)Success in time 0.197 s
%------------------------------------------------------------------------------
