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
% DateTime   : Thu Dec  3 12:46:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 222 expanded)
%              Number of leaves         :   19 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  377 (1139 expanded)
%              Number of equality atoms :   87 ( 231 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f73,f95,f105,f121,f146,f196,f225,f239])).

fof(f239,plain,
    ( ~ spl7_3
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f227,f161])).

fof(f161,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f36,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f227,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f67,f91])).

fof(f91,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f67,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f225,plain,
    ( spl7_1
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f223,f161])).

fof(f223,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | spl7_1
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f209,f51])).

fof(f51,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | k1_xboole_0 != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),X0) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK4(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK6(X0,X5))
                    & r2_hidden(sK6(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK4(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK4(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK4(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK6(X0,X5))
        & r2_hidden(sK6(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f209,plain,
    ( r2_hidden(sK1,k1_setfam_1(k1_xboole_0))
    | spl7_1
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f120,f199])).

fof(f199,plain,
    ( k1_xboole_0 = sK2
    | spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f198,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ( ~ r2_hidden(sK1,sK3)
        & r2_hidden(sK3,sK2) )
      | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & ( ! [X4] :
          ( r2_hidden(sK1,X4)
          | ~ r2_hidden(X4,sK2) )
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & r2_hidden(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_hidden(X3,X2) )
          | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r2_hidden(X4,X2) )
          | r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & r2_hidden(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ? [X3] :
            ( ~ r2_hidden(sK1,X3)
            & r2_hidden(X3,sK2) )
        | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
      & ( ! [X4] :
            ( r2_hidden(sK1,X4)
            | ~ r2_hidden(X4,sK2) )
        | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
      & r2_hidden(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK1,X3)
        & r2_hidden(X3,sK2) )
   => ( ~ r2_hidden(sK1,sK3)
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X4] :
            ( r2_hidden(X1,X4)
            | ~ r2_hidden(X4,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

fof(f198,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f197,f120])).

fof(f197,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl7_1 ),
    inference(superposition,[],[f60,f115])).

fof(f115,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f47,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f60,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_1
  <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f120,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_9
  <=> r2_hidden(sK1,k1_setfam_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f196,plain,
    ( spl7_7
    | spl7_9
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f195,f59,f119,f90])).

fof(f195,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f194,f30])).

fof(f194,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_1 ),
    inference(superposition,[],[f69,f115])).

fof(f69,plain,
    ( r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f146,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f144,f63])).

fof(f63,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f144,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(resolution,[],[f142,f67])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(sK1,X0) )
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f141,f75])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(sK1,X0)
        | k1_xboole_0 = sK2 )
    | ~ spl7_9 ),
    inference(resolution,[],[f120,f56])).

fof(f56,plain,(
    ! [X0,X7,X5] :
      ( ~ r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X7,X0)
      | r2_hidden(X5,X7)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f121,plain,
    ( spl7_7
    | spl7_9
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f117,f93,f119,f90])).

fof(f93,plain,
    ( spl7_8
  <=> ! [X0] :
        ( r2_hidden(X0,k1_setfam_1(sK2))
        | r2_hidden(sK1,sK6(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f117,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_8 ),
    inference(resolution,[],[f94,f54])).

fof(f54,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,sK6(X0,X5))
      | r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK6(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,sK6(sK2,X0))
        | r2_hidden(X0,k1_setfam_1(sK2)) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f105,plain,
    ( spl7_1
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f103,f31])).

fof(f31,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl7_1
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f97,f74])).

fof(f74,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f57,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f57,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl7_1
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f60,f91])).

fof(f95,plain,
    ( spl7_7
    | spl7_8
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f87,f71,f93,f90])).

fof(f71,plain,
    ( spl7_4
  <=> ! [X4] :
        ( r2_hidden(sK1,X4)
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f87,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_setfam_1(sK2))
        | k1_xboole_0 = sK2
        | r2_hidden(sK1,sK6(sK2,X0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f55,f72])).

fof(f72,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | r2_hidden(sK1,X4) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f55,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),X0)
      | r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK6(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f32,f71,f59])).

fof(f32,plain,(
    ! [X4] :
      ( r2_hidden(sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f33,f66,f59])).

fof(f33,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f34,f62,f59])).

fof(f34,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:36:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (1235)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (1242)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (1237)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (1245)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (1249)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (1237)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f64,f68,f73,f95,f105,f121,f146,f196,f225,f239])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    ~spl7_3 | ~spl7_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f238])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    $false | (~spl7_3 | ~spl7_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f227,f161])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(superposition,[],[f36,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_xboole_0) | (~spl7_3 | ~spl7_7)),
% 0.22/0.50    inference(backward_demodulation,[],[f67,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~spl7_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl7_7 <=> k1_xboole_0 = sK2),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    r2_hidden(sK3,sK2) | ~spl7_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl7_3 <=> r2_hidden(sK3,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    spl7_1 | ~spl7_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f224])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    $false | (spl7_1 | ~spl7_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f223,f161])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    r2_hidden(sK1,k1_xboole_0) | (spl7_1 | ~spl7_9)),
% 0.22/0.50    inference(forward_demodulation,[],[f209,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 0.22/0.50    inference(equality_resolution,[],[f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | k1_xboole_0 != X0) )),
% 0.22/0.50    inference(equality_resolution,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | k1_xboole_0 != X1 | k1_xboole_0 != X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.22/0.50    inference(rectify,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    r2_hidden(sK1,k1_setfam_1(k1_xboole_0)) | (spl7_1 | ~spl7_9)),
% 0.22/0.50    inference(backward_demodulation,[],[f120,f199])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | (spl7_1 | ~spl7_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f198,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ((~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f22,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) => (~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(rectify,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl7_1 | ~spl7_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f197,f120])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    ~r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl7_1),
% 0.22/0.50    inference(superposition,[],[f60,f115])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f112])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.22/0.50    inference(superposition,[],[f47,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl7_1 <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    r2_hidden(sK1,k1_setfam_1(sK2)) | ~spl7_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl7_9 <=> r2_hidden(sK1,k1_setfam_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    spl7_7 | spl7_9 | ~spl7_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f195,f59,f119,f90])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl7_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f194,f30])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl7_1),
% 0.22/0.50    inference(superposition,[],[f69,f115])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | ~spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    spl7_2 | ~spl7_3 | ~spl7_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f145])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    $false | (spl7_2 | ~spl7_3 | ~spl7_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f144,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ~r2_hidden(sK1,sK3) | spl7_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl7_2 <=> r2_hidden(sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    r2_hidden(sK1,sK3) | (~spl7_3 | ~spl7_9)),
% 0.22/0.50    inference(resolution,[],[f142,f67])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(sK1,X0)) ) | ~spl7_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f141,f75])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(sK1,X0) | k1_xboole_0 = sK2) ) | ~spl7_9),
% 0.22/0.50    inference(resolution,[],[f120,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0,X7,X5] : (~r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X7,X0) | r2_hidden(X5,X7) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(equality_resolution,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl7_7 | spl7_9 | ~spl7_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f117,f93,f119,f90])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl7_8 <=> ! [X0] : (r2_hidden(X0,k1_setfam_1(sK2)) | r2_hidden(sK1,sK6(sK2,X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl7_8),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f116])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    r2_hidden(sK1,k1_setfam_1(sK2)) | r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl7_8),
% 0.22/0.50    inference(resolution,[],[f94,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X5] : (~r2_hidden(X5,sK6(X0,X5)) | r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(equality_resolution,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK6(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK1,sK6(sK2,X0)) | r2_hidden(X0,k1_setfam_1(sK2))) ) | ~spl7_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f93])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl7_1 | ~spl7_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f104])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    $false | (spl7_1 | ~spl7_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f103,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    r2_hidden(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ~r2_hidden(sK1,sK0) | (spl7_1 | ~spl7_7)),
% 0.22/0.50    inference(forward_demodulation,[],[f97,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f57,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(equality_resolution,[],[f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | (spl7_1 | ~spl7_7)),
% 0.22/0.50    inference(backward_demodulation,[],[f60,f91])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl7_7 | spl7_8 | ~spl7_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f87,f71,f93,f90])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    spl7_4 <=> ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | r2_hidden(sK1,sK6(sK2,X0))) ) | ~spl7_4),
% 0.22/0.50    inference(resolution,[],[f55,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X4] : (~r2_hidden(X4,sK2) | r2_hidden(sK1,X4)) ) | ~spl7_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f71])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),X0) | r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(equality_resolution,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK6(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl7_1 | spl7_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f71,f59])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ~spl7_1 | spl7_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f66,f59])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    r2_hidden(sK3,sK2) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ~spl7_1 | ~spl7_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f62,f59])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (1237)------------------------------
% 0.22/0.50  % (1237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1237)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (1237)Memory used [KB]: 10746
% 0.22/0.50  % (1237)Time elapsed: 0.052 s
% 0.22/0.50  % (1237)------------------------------
% 0.22/0.50  % (1237)------------------------------
% 0.22/0.50  % (1247)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (1234)Success in time 0.132 s
%------------------------------------------------------------------------------
