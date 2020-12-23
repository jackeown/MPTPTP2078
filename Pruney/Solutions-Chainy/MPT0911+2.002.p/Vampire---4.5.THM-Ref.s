%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:28 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 322 expanded)
%              Number of leaves         :   21 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  389 (1425 expanded)
%              Number of equality atoms :  197 ( 775 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1839,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f527,f1635,f1836])).

fof(f1836,plain,(
    ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f1835])).

fof(f1835,plain,
    ( $false
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1735,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1735,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl11_2 ),
    inference(backward_demodulation,[],[f183,f420])).

fof(f420,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f419,f62])).

fof(f62,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f29,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f419,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK0 )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f418,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f418,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f417,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f42])).

fof(f417,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f385,f258])).

fof(f258,plain,
    ( ! [X4] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f248,f234])).

fof(f234,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl11_2 ),
    inference(superposition,[],[f123,f157])).

fof(f157,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_2 ),
    inference(resolution,[],[f153,f130])).

fof(f130,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f72,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
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

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f47])).

fof(f47,plain,(
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

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f153,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl11_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f123,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f106,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f99,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f248,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X4) ),
    inference(superposition,[],[f124,f123])).

fof(f124,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f105,f107])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f385,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl11_2 ),
    inference(superposition,[],[f120,f157])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f102,f107])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f183,plain,(
    ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f172,f67])).

fof(f172,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(extensionality_resolution,[],[f87,f64])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1635,plain,(
    ~ spl11_1 ),
    inference(avatar_contradiction_clause,[],[f1634])).

fof(f1634,plain,
    ( $false
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f1633,f591])).

fof(f591,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl11_1 ),
    inference(resolution,[],[f583,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f583,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl11_1 ),
    inference(resolution,[],[f93,f149])).

fof(f149,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl11_1
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f1633,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f1632,f761])).

fof(f761,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(superposition,[],[f65,f759])).

fof(f759,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f758,f62])).

fof(f758,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f757,f63])).

fof(f757,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f751,f64])).

fof(f751,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f113,f109])).

fof(f109,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f60,f91])).

fof(f60,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f96,f91])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f65,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f1632,plain,
    ( sK3 = k2_mcart_1(sK4)
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl11_1 ),
    inference(trivial_inequality_removal,[],[f1631])).

fof(f1631,plain,
    ( sK4 != sK4
    | sK3 = k2_mcart_1(sK4)
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl11_1 ),
    inference(superposition,[],[f741,f714])).

fof(f714,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f706,f705])).

fof(f705,plain,
    ( k1_mcart_1(sK4) = sK9(sK4)
    | ~ spl11_1 ),
    inference(superposition,[],[f76,f697])).

fof(f697,plain,
    ( sK4 = k4_tarski(sK9(sK4),sK10(sK4))
    | ~ spl11_1 ),
    inference(resolution,[],[f98,f149])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK9(X0),sK10(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK9(X0),sK10(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f39,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK9(X0),sK10(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f76,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f706,plain,
    ( sK4 = k4_tarski(sK9(sK4),k2_mcart_1(sK4))
    | ~ spl11_1 ),
    inference(backward_demodulation,[],[f697,f704])).

fof(f704,plain,
    ( k2_mcart_1(sK4) = sK10(sK4)
    | ~ spl11_1 ),
    inference(superposition,[],[f77,f697])).

fof(f77,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f23])).

fof(f741,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | sK3 = X0
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f740,f580])).

fof(f580,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl11_1 ),
    inference(resolution,[],[f575,f84])).

fof(f575,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl11_1 ),
    inference(resolution,[],[f568,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f568,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl11_1 ),
    inference(resolution,[],[f92,f149])).

fof(f740,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | sK3 = X0
        | ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) )
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f739,f595])).

fof(f595,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl11_1 ),
    inference(resolution,[],[f582,f84])).

fof(f582,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl11_1 ),
    inference(resolution,[],[f93,f568])).

fof(f739,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | sK3 = X0
        | ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) )
    | ~ spl11_1 ),
    inference(superposition,[],[f108,f723])).

fof(f723,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f722,f719])).

fof(f719,plain,
    ( k1_mcart_1(k1_mcart_1(sK4)) = sK9(k1_mcart_1(sK4))
    | ~ spl11_1 ),
    inference(superposition,[],[f76,f696])).

fof(f696,plain,
    ( k1_mcart_1(sK4) = k4_tarski(sK9(k1_mcart_1(sK4)),sK10(k1_mcart_1(sK4)))
    | ~ spl11_1 ),
    inference(resolution,[],[f98,f568])).

fof(f722,plain,
    ( k1_mcart_1(sK4) = k4_tarski(sK9(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl11_1 ),
    inference(backward_demodulation,[],[f696,f718])).

fof(f718,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) = sK10(k1_mcart_1(sK4))
    | ~ spl11_1 ),
    inference(superposition,[],[f77,f696])).

fof(f108,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f61,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f527,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f526,f151,f147])).

fof(f526,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f109,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:13:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (18690)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (18682)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (18674)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (18672)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (18670)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (18687)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (18671)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (18676)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (18686)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (18688)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (18667)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (18668)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (18668)Refutation not found, incomplete strategy% (18668)------------------------------
% 0.21/0.54  % (18668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18668)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18668)Memory used [KB]: 1663
% 0.21/0.54  % (18668)Time elapsed: 0.123 s
% 0.21/0.54  % (18668)------------------------------
% 0.21/0.54  % (18668)------------------------------
% 0.21/0.54  % (18675)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (18695)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.41/0.55  % (18680)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.41/0.55  % (18669)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.41/0.55  % (18678)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.55  % (18679)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.41/0.55  % (18679)Refutation not found, incomplete strategy% (18679)------------------------------
% 1.41/0.55  % (18679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (18679)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (18679)Memory used [KB]: 10618
% 1.41/0.55  % (18679)Time elapsed: 0.139 s
% 1.41/0.55  % (18679)------------------------------
% 1.41/0.55  % (18679)------------------------------
% 1.41/0.55  % (18677)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.55  % (18691)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.55  % (18677)Refutation not found, incomplete strategy% (18677)------------------------------
% 1.41/0.55  % (18677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (18677)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (18677)Memory used [KB]: 10874
% 1.41/0.55  % (18677)Time elapsed: 0.139 s
% 1.41/0.55  % (18677)------------------------------
% 1.41/0.55  % (18677)------------------------------
% 1.41/0.56  % (18696)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.56  % (18696)Refutation not found, incomplete strategy% (18696)------------------------------
% 1.41/0.56  % (18696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (18696)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (18696)Memory used [KB]: 1663
% 1.41/0.56  % (18696)Time elapsed: 0.002 s
% 1.41/0.56  % (18696)------------------------------
% 1.41/0.56  % (18696)------------------------------
% 1.41/0.56  % (18691)Refutation not found, incomplete strategy% (18691)------------------------------
% 1.41/0.56  % (18691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (18691)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (18691)Memory used [KB]: 10746
% 1.41/0.56  % (18691)Time elapsed: 0.146 s
% 1.41/0.56  % (18691)------------------------------
% 1.41/0.56  % (18691)------------------------------
% 1.41/0.56  % (18693)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.56  % (18683)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.56  % (18673)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.57  % (18694)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.55/0.57  % (18695)Refutation not found, incomplete strategy% (18695)------------------------------
% 1.55/0.57  % (18695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (18695)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (18695)Memory used [KB]: 10874
% 1.55/0.57  % (18695)Time elapsed: 0.155 s
% 1.55/0.57  % (18695)------------------------------
% 1.55/0.57  % (18695)------------------------------
% 1.55/0.57  % (18694)Refutation not found, incomplete strategy% (18694)------------------------------
% 1.55/0.57  % (18694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (18694)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (18694)Memory used [KB]: 6268
% 1.55/0.57  % (18694)Time elapsed: 0.159 s
% 1.55/0.57  % (18694)------------------------------
% 1.55/0.57  % (18694)------------------------------
% 1.55/0.57  % (18684)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.55/0.57  % (18685)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.55/0.57  % (18685)Refutation not found, incomplete strategy% (18685)------------------------------
% 1.55/0.57  % (18685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (18685)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (18685)Memory used [KB]: 1791
% 1.55/0.57  % (18685)Time elapsed: 0.160 s
% 1.55/0.57  % (18685)------------------------------
% 1.55/0.57  % (18685)------------------------------
% 1.55/0.58  % (18683)Refutation not found, incomplete strategy% (18683)------------------------------
% 1.55/0.58  % (18683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (18693)Refutation not found, incomplete strategy% (18693)------------------------------
% 1.55/0.58  % (18693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (18693)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (18693)Memory used [KB]: 6268
% 1.55/0.58  % (18693)Time elapsed: 0.149 s
% 1.55/0.58  % (18693)------------------------------
% 1.55/0.58  % (18693)------------------------------
% 1.55/0.58  % (18683)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (18683)Memory used [KB]: 10746
% 1.55/0.58  % (18683)Time elapsed: 0.168 s
% 1.55/0.58  % (18683)------------------------------
% 1.55/0.58  % (18683)------------------------------
% 1.55/0.58  % (18692)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.55/0.58  % (18689)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.55/0.59  % (18681)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.60  % (18684)Refutation not found, incomplete strategy% (18684)------------------------------
% 1.55/0.60  % (18684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (18684)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.60  
% 1.55/0.60  % (18684)Memory used [KB]: 1918
% 1.55/0.60  % (18684)Time elapsed: 0.186 s
% 1.55/0.60  % (18684)------------------------------
% 1.55/0.60  % (18684)------------------------------
% 1.55/0.61  % (18681)Refutation not found, incomplete strategy% (18681)------------------------------
% 1.55/0.61  % (18681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (18681)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (18681)Memory used [KB]: 1791
% 1.55/0.61  % (18681)Time elapsed: 0.159 s
% 1.55/0.61  % (18681)------------------------------
% 1.55/0.61  % (18681)------------------------------
% 1.99/0.65  % (18682)Refutation not found, incomplete strategy% (18682)------------------------------
% 1.99/0.65  % (18682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.65  % (18682)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.65  
% 1.99/0.65  % (18682)Memory used [KB]: 6140
% 1.99/0.65  % (18682)Time elapsed: 0.172 s
% 1.99/0.65  % (18682)------------------------------
% 1.99/0.65  % (18682)------------------------------
% 1.99/0.66  % (18718)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.17/0.67  % (18667)Refutation not found, incomplete strategy% (18667)------------------------------
% 2.17/0.67  % (18667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.67  % (18667)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.67  
% 2.17/0.67  % (18667)Memory used [KB]: 1663
% 2.17/0.67  % (18667)Time elapsed: 0.246 s
% 2.17/0.67  % (18667)------------------------------
% 2.17/0.67  % (18667)------------------------------
% 2.17/0.68  % (18673)Refutation found. Thanks to Tanya!
% 2.17/0.68  % SZS status Theorem for theBenchmark
% 2.17/0.68  % SZS output start Proof for theBenchmark
% 2.17/0.68  fof(f1839,plain,(
% 2.17/0.68    $false),
% 2.17/0.68    inference(avatar_sat_refutation,[],[f527,f1635,f1836])).
% 2.17/0.68  fof(f1836,plain,(
% 2.17/0.68    ~spl11_2),
% 2.17/0.68    inference(avatar_contradiction_clause,[],[f1835])).
% 2.17/0.68  fof(f1835,plain,(
% 2.17/0.68    $false | ~spl11_2),
% 2.17/0.68    inference(subsumption_resolution,[],[f1735,f67])).
% 2.17/0.68  fof(f67,plain,(
% 2.17/0.68    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f6])).
% 2.17/0.68  fof(f6,axiom,(
% 2.17/0.68    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.17/0.68  fof(f1735,plain,(
% 2.17/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl11_2),
% 2.17/0.68    inference(backward_demodulation,[],[f183,f420])).
% 2.17/0.68  fof(f420,plain,(
% 2.17/0.68    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl11_2),
% 2.17/0.68    inference(subsumption_resolution,[],[f419,f62])).
% 2.17/0.68  fof(f62,plain,(
% 2.17/0.68    k1_xboole_0 != sK0),
% 2.17/0.68    inference(cnf_transformation,[],[f42])).
% 2.17/0.68  fof(f42,plain,(
% 2.17/0.68    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.17/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f29,f41])).
% 2.17/0.68  fof(f41,plain,(
% 2.17/0.68    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 2.17/0.68    introduced(choice_axiom,[])).
% 2.17/0.68  fof(f29,plain,(
% 2.17/0.68    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.17/0.68    inference(flattening,[],[f28])).
% 2.17/0.68  fof(f28,plain,(
% 2.17/0.68    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.17/0.68    inference(ennf_transformation,[],[f25])).
% 2.17/0.68  fof(f25,negated_conjecture,(
% 2.17/0.68    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.17/0.68    inference(negated_conjecture,[],[f24])).
% 2.17/0.68  fof(f24,conjecture,(
% 2.17/0.68    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 2.17/0.68  fof(f419,plain,(
% 2.17/0.68    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK0) ) | ~spl11_2),
% 2.17/0.68    inference(subsumption_resolution,[],[f418,f63])).
% 2.17/0.68  fof(f63,plain,(
% 2.17/0.68    k1_xboole_0 != sK1),
% 2.17/0.68    inference(cnf_transformation,[],[f42])).
% 2.17/0.68  fof(f418,plain,(
% 2.17/0.68    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl11_2),
% 2.17/0.68    inference(subsumption_resolution,[],[f417,f64])).
% 2.17/0.68  fof(f64,plain,(
% 2.17/0.68    k1_xboole_0 != sK2),
% 2.17/0.68    inference(cnf_transformation,[],[f42])).
% 2.17/0.68  fof(f417,plain,(
% 2.17/0.68    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl11_2),
% 2.17/0.68    inference(subsumption_resolution,[],[f385,f258])).
% 2.17/0.68  fof(f258,plain,(
% 2.17/0.68    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)) ) | ~spl11_2),
% 2.17/0.68    inference(forward_demodulation,[],[f248,f234])).
% 2.17/0.68  fof(f234,plain,(
% 2.17/0.68    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~spl11_2),
% 2.17/0.68    inference(superposition,[],[f123,f157])).
% 2.17/0.68  fof(f157,plain,(
% 2.17/0.68    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_2),
% 2.17/0.68    inference(resolution,[],[f153,f130])).
% 2.17/0.68  fof(f130,plain,(
% 2.17/0.68    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 2.17/0.68    inference(resolution,[],[f72,f70])).
% 2.17/0.68  fof(f70,plain,(
% 2.17/0.68    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f46])).
% 2.17/0.68  fof(f46,plain,(
% 2.17/0.68    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.17/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 2.17/0.68  fof(f45,plain,(
% 2.17/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 2.17/0.68    introduced(choice_axiom,[])).
% 2.17/0.68  fof(f44,plain,(
% 2.17/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.17/0.68    inference(rectify,[],[f43])).
% 2.17/0.68  fof(f43,plain,(
% 2.17/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.17/0.68    inference(nnf_transformation,[],[f1])).
% 2.17/0.68  fof(f1,axiom,(
% 2.17/0.68    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.17/0.68  fof(f72,plain,(
% 2.17/0.68    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.17/0.68    inference(cnf_transformation,[],[f48])).
% 2.17/0.68  fof(f48,plain,(
% 2.17/0.68    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 2.17/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f47])).
% 2.17/0.68  fof(f47,plain,(
% 2.17/0.68    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 2.17/0.68    introduced(choice_axiom,[])).
% 2.17/0.68  fof(f30,plain,(
% 2.17/0.68    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.17/0.68    inference(ennf_transformation,[],[f20])).
% 2.17/0.68  fof(f20,axiom,(
% 2.17/0.68    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 2.17/0.68  fof(f153,plain,(
% 2.17/0.68    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl11_2),
% 2.17/0.68    inference(avatar_component_clause,[],[f151])).
% 2.17/0.68  fof(f151,plain,(
% 2.17/0.68    spl11_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.17/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 2.17/0.68  fof(f123,plain,(
% 2.17/0.68    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 2.17/0.68    inference(equality_resolution,[],[f116])).
% 2.17/0.68  fof(f116,plain,(
% 2.17/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.17/0.68    inference(definition_unfolding,[],[f106,f107])).
% 2.17/0.68  fof(f107,plain,(
% 2.17/0.68    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.17/0.68    inference(definition_unfolding,[],[f99,f91])).
% 2.17/0.68  fof(f91,plain,(
% 2.17/0.68    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f17])).
% 2.17/0.68  fof(f17,axiom,(
% 2.17/0.68    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.17/0.68  fof(f99,plain,(
% 2.17/0.68    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f18])).
% 2.17/0.68  fof(f18,axiom,(
% 2.17/0.68    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 2.17/0.68  fof(f106,plain,(
% 2.17/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f59])).
% 2.17/0.68  fof(f59,plain,(
% 2.17/0.68    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.17/0.68    inference(flattening,[],[f58])).
% 2.17/0.68  fof(f58,plain,(
% 2.17/0.68    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.17/0.68    inference(nnf_transformation,[],[f22])).
% 2.17/0.68  fof(f22,axiom,(
% 2.17/0.68    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 2.17/0.68  fof(f248,plain,(
% 2.17/0.68    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X4)) )),
% 2.17/0.68    inference(superposition,[],[f124,f123])).
% 2.17/0.68  fof(f124,plain,(
% 2.17/0.68    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 2.17/0.68    inference(equality_resolution,[],[f117])).
% 2.17/0.68  fof(f117,plain,(
% 2.17/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.17/0.68    inference(definition_unfolding,[],[f105,f107])).
% 2.17/0.68  fof(f105,plain,(
% 2.17/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f59])).
% 2.17/0.68  fof(f385,plain,(
% 2.17/0.68    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl11_2),
% 2.17/0.68    inference(superposition,[],[f120,f157])).
% 2.17/0.68  fof(f120,plain,(
% 2.17/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.17/0.68    inference(definition_unfolding,[],[f102,f107])).
% 2.17/0.68  fof(f102,plain,(
% 2.17/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.17/0.68    inference(cnf_transformation,[],[f59])).
% 2.17/0.68  fof(f183,plain,(
% 2.17/0.68    ~r1_tarski(sK2,k1_xboole_0)),
% 2.17/0.68    inference(subsumption_resolution,[],[f172,f67])).
% 2.17/0.68  fof(f172,plain,(
% 2.17/0.68    ~r1_tarski(sK2,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK2)),
% 2.17/0.68    inference(extensionality_resolution,[],[f87,f64])).
% 2.17/0.68  fof(f87,plain,(
% 2.17/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f54])).
% 2.17/0.68  fof(f54,plain,(
% 2.17/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.68    inference(flattening,[],[f53])).
% 2.17/0.68  fof(f53,plain,(
% 2.17/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.68    inference(nnf_transformation,[],[f4])).
% 2.17/0.68  fof(f4,axiom,(
% 2.17/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.17/0.68  fof(f1635,plain,(
% 2.17/0.68    ~spl11_1),
% 2.17/0.68    inference(avatar_contradiction_clause,[],[f1634])).
% 2.17/0.68  fof(f1634,plain,(
% 2.17/0.68    $false | ~spl11_1),
% 2.17/0.68    inference(subsumption_resolution,[],[f1633,f591])).
% 2.17/0.68  fof(f591,plain,(
% 2.17/0.68    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl11_1),
% 2.17/0.68    inference(resolution,[],[f583,f84])).
% 2.17/0.68  fof(f84,plain,(
% 2.17/0.68    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f35])).
% 2.17/0.68  fof(f35,plain,(
% 2.17/0.68    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.17/0.68    inference(ennf_transformation,[],[f12])).
% 2.17/0.68  fof(f12,axiom,(
% 2.17/0.68    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 2.17/0.68  fof(f583,plain,(
% 2.17/0.68    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl11_1),
% 2.17/0.68    inference(resolution,[],[f93,f149])).
% 2.17/0.68  fof(f149,plain,(
% 2.17/0.68    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl11_1),
% 2.17/0.68    inference(avatar_component_clause,[],[f147])).
% 2.17/0.68  fof(f147,plain,(
% 2.17/0.68    spl11_1 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.17/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 2.17/0.68  fof(f93,plain,(
% 2.17/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f36])).
% 2.17/0.68  fof(f36,plain,(
% 2.17/0.68    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.17/0.68    inference(ennf_transformation,[],[f19])).
% 2.17/0.68  fof(f19,axiom,(
% 2.17/0.68    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 2.17/0.68  fof(f1633,plain,(
% 2.17/0.68    ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl11_1),
% 2.17/0.68    inference(subsumption_resolution,[],[f1632,f761])).
% 2.17/0.68  fof(f761,plain,(
% 2.17/0.68    sK3 != k2_mcart_1(sK4)),
% 2.17/0.68    inference(superposition,[],[f65,f759])).
% 2.17/0.68  fof(f759,plain,(
% 2.17/0.68    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 2.17/0.68    inference(subsumption_resolution,[],[f758,f62])).
% 2.17/0.68  fof(f758,plain,(
% 2.17/0.68    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK0),
% 2.17/0.68    inference(subsumption_resolution,[],[f757,f63])).
% 2.17/0.68  fof(f757,plain,(
% 2.17/0.68    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 2.17/0.68    inference(subsumption_resolution,[],[f751,f64])).
% 2.17/0.68  fof(f751,plain,(
% 2.17/0.68    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 2.17/0.68    inference(resolution,[],[f113,f109])).
% 2.17/0.68  fof(f109,plain,(
% 2.17/0.68    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.17/0.68    inference(definition_unfolding,[],[f60,f91])).
% 2.17/0.68  fof(f60,plain,(
% 2.17/0.68    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.17/0.68    inference(cnf_transformation,[],[f42])).
% 2.17/0.68  fof(f113,plain,(
% 2.17/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.17/0.68    inference(definition_unfolding,[],[f96,f91])).
% 2.17/0.68  fof(f96,plain,(
% 2.17/0.68    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.17/0.68    inference(cnf_transformation,[],[f37])).
% 2.17/0.68  fof(f37,plain,(
% 2.17/0.68    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.17/0.68    inference(ennf_transformation,[],[f21])).
% 2.17/0.68  fof(f21,axiom,(
% 2.17/0.68    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 2.17/0.68  fof(f65,plain,(
% 2.17/0.68    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 2.17/0.68    inference(cnf_transformation,[],[f42])).
% 2.17/0.68  fof(f1632,plain,(
% 2.17/0.68    sK3 = k2_mcart_1(sK4) | ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl11_1),
% 2.17/0.68    inference(trivial_inequality_removal,[],[f1631])).
% 2.17/0.68  fof(f1631,plain,(
% 2.17/0.68    sK4 != sK4 | sK3 = k2_mcart_1(sK4) | ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl11_1),
% 2.17/0.68    inference(superposition,[],[f741,f714])).
% 2.17/0.68  fof(f714,plain,(
% 2.17/0.68    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl11_1),
% 2.17/0.68    inference(forward_demodulation,[],[f706,f705])).
% 2.17/0.68  fof(f705,plain,(
% 2.17/0.68    k1_mcart_1(sK4) = sK9(sK4) | ~spl11_1),
% 2.17/0.68    inference(superposition,[],[f76,f697])).
% 2.17/0.68  fof(f697,plain,(
% 2.17/0.68    sK4 = k4_tarski(sK9(sK4),sK10(sK4)) | ~spl11_1),
% 2.17/0.68    inference(resolution,[],[f98,f149])).
% 2.17/0.68  fof(f98,plain,(
% 2.17/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK9(X0),sK10(X0)) = X0) )),
% 2.17/0.68    inference(cnf_transformation,[],[f57])).
% 2.17/0.68  fof(f57,plain,(
% 2.17/0.68    ! [X0,X1,X2] : (k4_tarski(sK9(X0),sK10(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.17/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f39,f56])).
% 2.17/0.68  fof(f56,plain,(
% 2.17/0.68    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK9(X0),sK10(X0)) = X0)),
% 2.17/0.68    introduced(choice_axiom,[])).
% 2.17/0.68  fof(f39,plain,(
% 2.17/0.68    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.17/0.68    inference(ennf_transformation,[],[f9])).
% 2.17/0.68  fof(f9,axiom,(
% 2.17/0.68    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 2.17/0.68  fof(f76,plain,(
% 2.17/0.68    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.17/0.68    inference(cnf_transformation,[],[f23])).
% 2.17/0.68  fof(f23,axiom,(
% 2.17/0.68    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 2.17/0.68  fof(f706,plain,(
% 2.17/0.68    sK4 = k4_tarski(sK9(sK4),k2_mcart_1(sK4)) | ~spl11_1),
% 2.17/0.68    inference(backward_demodulation,[],[f697,f704])).
% 2.17/0.68  fof(f704,plain,(
% 2.17/0.68    k2_mcart_1(sK4) = sK10(sK4) | ~spl11_1),
% 2.17/0.68    inference(superposition,[],[f77,f697])).
% 2.17/0.68  fof(f77,plain,(
% 2.17/0.68    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.17/0.68    inference(cnf_transformation,[],[f23])).
% 2.17/0.68  fof(f741,plain,(
% 2.17/0.68    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = X0 | ~m1_subset_1(X0,sK2)) ) | ~spl11_1),
% 2.17/0.68    inference(subsumption_resolution,[],[f740,f580])).
% 2.17/0.68  fof(f580,plain,(
% 2.17/0.68    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl11_1),
% 2.17/0.68    inference(resolution,[],[f575,f84])).
% 2.17/0.68  fof(f575,plain,(
% 2.17/0.68    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl11_1),
% 2.17/0.68    inference(resolution,[],[f568,f92])).
% 2.17/0.68  fof(f92,plain,(
% 2.17/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f36])).
% 2.17/0.68  fof(f568,plain,(
% 2.17/0.68    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl11_1),
% 2.17/0.68    inference(resolution,[],[f92,f149])).
% 2.17/0.68  fof(f740,plain,(
% 2.17/0.68    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = X0 | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)) ) | ~spl11_1),
% 2.17/0.68    inference(subsumption_resolution,[],[f739,f595])).
% 2.17/0.68  fof(f595,plain,(
% 2.17/0.68    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl11_1),
% 2.17/0.68    inference(resolution,[],[f582,f84])).
% 2.17/0.68  fof(f582,plain,(
% 2.17/0.68    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl11_1),
% 2.17/0.68    inference(resolution,[],[f93,f568])).
% 2.17/0.68  fof(f739,plain,(
% 2.17/0.68    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = X0 | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)) ) | ~spl11_1),
% 2.17/0.68    inference(superposition,[],[f108,f723])).
% 2.17/0.68  fof(f723,plain,(
% 2.17/0.68    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl11_1),
% 2.17/0.68    inference(forward_demodulation,[],[f722,f719])).
% 2.17/0.68  fof(f719,plain,(
% 2.17/0.68    k1_mcart_1(k1_mcart_1(sK4)) = sK9(k1_mcart_1(sK4)) | ~spl11_1),
% 2.17/0.68    inference(superposition,[],[f76,f696])).
% 2.17/0.68  fof(f696,plain,(
% 2.17/0.68    k1_mcart_1(sK4) = k4_tarski(sK9(k1_mcart_1(sK4)),sK10(k1_mcart_1(sK4))) | ~spl11_1),
% 2.17/0.68    inference(resolution,[],[f98,f568])).
% 2.17/0.68  fof(f722,plain,(
% 2.17/0.68    k1_mcart_1(sK4) = k4_tarski(sK9(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl11_1),
% 2.17/0.68    inference(backward_demodulation,[],[f696,f718])).
% 2.17/0.68  fof(f718,plain,(
% 2.17/0.68    k2_mcart_1(k1_mcart_1(sK4)) = sK10(k1_mcart_1(sK4)) | ~spl11_1),
% 2.17/0.68    inference(superposition,[],[f77,f696])).
% 2.17/0.68  fof(f108,plain,(
% 2.17/0.68    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 2.17/0.68    inference(definition_unfolding,[],[f61,f90])).
% 2.17/0.68  fof(f90,plain,(
% 2.17/0.68    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f16])).
% 2.17/0.68  fof(f16,axiom,(
% 2.17/0.68    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.17/0.68  fof(f61,plain,(
% 2.17/0.68    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f42])).
% 2.17/0.68  fof(f527,plain,(
% 2.17/0.68    spl11_1 | spl11_2),
% 2.17/0.68    inference(avatar_split_clause,[],[f526,f151,f147])).
% 2.17/0.68  fof(f526,plain,(
% 2.17/0.68    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.17/0.68    inference(resolution,[],[f109,f83])).
% 2.17/0.68  fof(f83,plain,(
% 2.17/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f34])).
% 2.17/0.68  fof(f34,plain,(
% 2.17/0.68    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.17/0.68    inference(flattening,[],[f33])).
% 2.17/0.68  fof(f33,plain,(
% 2.17/0.68    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.17/0.68    inference(ennf_transformation,[],[f13])).
% 2.17/0.68  fof(f13,axiom,(
% 2.17/0.68    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 2.17/0.68  % SZS output end Proof for theBenchmark
% 2.17/0.68  % (18673)------------------------------
% 2.17/0.68  % (18673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (18673)Termination reason: Refutation
% 2.17/0.68  
% 2.17/0.68  % (18673)Memory used [KB]: 11641
% 2.17/0.68  % (18673)Time elapsed: 0.244 s
% 2.17/0.68  % (18673)------------------------------
% 2.17/0.68  % (18673)------------------------------
% 2.17/0.69  % (18666)Success in time 0.318 s
%------------------------------------------------------------------------------
