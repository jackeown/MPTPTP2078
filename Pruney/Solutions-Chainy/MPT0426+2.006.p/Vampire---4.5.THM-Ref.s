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
% DateTime   : Thu Dec  3 12:46:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 231 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  393 (1145 expanded)
%              Number of equality atoms :   75 ( 186 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f263,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f73,f90,f109,f156,f167,f178,f183,f192,f197,f228,f256])).

fof(f256,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_18 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl7_1
    | ~ spl7_12
    | spl7_18 ),
    inference(subsumption_resolution,[],[f254,f31])).

fof(f31,plain,(
    r2_hidden(sK1,sK0) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

fof(f254,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl7_1
    | ~ spl7_12
    | spl7_18 ),
    inference(forward_demodulation,[],[f241,f74])).

fof(f74,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f57,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f57,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f241,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl7_1
    | ~ spl7_12
    | spl7_18 ),
    inference(backward_demodulation,[],[f60,f239])).

fof(f239,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_12
    | spl7_18 ),
    inference(subsumption_resolution,[],[f238,f227])).

fof(f227,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl7_18
  <=> r2_hidden(sK1,k1_setfam_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f238,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_12 ),
    inference(duplicate_literal_removal,[],[f237])).

fof(f237,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_12 ),
    inference(resolution,[],[f108,f54])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f108,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,sK6(sK2,X0))
        | r2_hidden(X0,k1_setfam_1(sK2)) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_12
  <=> ! [X0] :
        ( r2_hidden(X0,k1_setfam_1(sK2))
        | r2_hidden(sK1,sK6(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f60,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_1
  <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f228,plain,
    ( spl7_11
    | ~ spl7_18
    | spl7_1 ),
    inference(avatar_split_clause,[],[f226,f59,f154,f104])).

fof(f104,plain,
    ( spl7_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f226,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | spl7_1 ),
    inference(subsumption_resolution,[],[f198,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f198,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl7_1 ),
    inference(superposition,[],[f60,f116])).

fof(f116,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f197,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f193,f63])).

fof(f63,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f193,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f72,f67])).

fof(f67,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f72,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | r2_hidden(sK1,X4) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl7_4
  <=> ! [X4] :
        ( r2_hidden(sK1,X4)
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f192,plain,
    ( spl7_11
    | spl7_4
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f191,f154,f71,f104])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(sK1,X0)
        | k1_xboole_0 = sK2 )
    | ~ spl7_18 ),
    inference(resolution,[],[f155,f56])).

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

fof(f155,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f154])).

fof(f183,plain,(
    ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl7_8 ),
    inference(resolution,[],[f89,f35])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f89,plain,
    ( ! [X1] : ~ v1_xboole_0(X1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_8
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f178,plain,
    ( spl7_1
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl7_1
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f176,f31])).

fof(f176,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl7_1
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f175,f74])).

fof(f175,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl7_1
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f60,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f167,plain,
    ( ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f158,f86])).

fof(f86,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_7
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f158,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f67,f105])).

fof(f156,plain,
    ( spl7_11
    | spl7_18
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f152,f59,f154,f104])).

fof(f152,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f151,f30])).

fof(f151,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_1 ),
    inference(superposition,[],[f69,f116])).

fof(f69,plain,
    ( r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f109,plain,
    ( spl7_11
    | spl7_12
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f102,f71,f107,f104])).

fof(f102,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_setfam_1(sK2))
        | k1_xboole_0 = sK2
        | r2_hidden(sK1,sK6(sK2,X0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f55,f72])).

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

fof(f90,plain,
    ( spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f76,f88,f85])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f49,f36])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (7861)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.46  % (7869)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.47  % (7859)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.48  % (7856)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.49  % (7871)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.49  % (7868)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (7857)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (7868)Refutation not found, incomplete strategy% (7868)------------------------------
% 0.19/0.49  % (7868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (7868)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (7868)Memory used [KB]: 6140
% 0.19/0.49  % (7868)Time elapsed: 0.074 s
% 0.19/0.49  % (7868)------------------------------
% 0.19/0.49  % (7868)------------------------------
% 0.19/0.49  % (7860)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.49  % (7863)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.50  % (7864)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.50  % (7858)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.50  % (7876)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.50  % (7874)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.50  % (7872)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.50  % (7858)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f263,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f64,f68,f73,f90,f109,f156,f167,f178,f183,f192,f197,f228,f256])).
% 0.19/0.50  fof(f256,plain,(
% 0.19/0.50    spl7_1 | ~spl7_12 | spl7_18),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f255])).
% 0.19/0.50  fof(f255,plain,(
% 0.19/0.50    $false | (spl7_1 | ~spl7_12 | spl7_18)),
% 0.19/0.50    inference(subsumption_resolution,[],[f254,f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    r2_hidden(sK1,sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ((~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f22,f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) => (~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.50    inference(rectify,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.50    inference(flattening,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.50    inference(nnf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,plain,(
% 0.19/0.50    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.50    inference(flattening,[],[f10])).
% 0.19/0.50  fof(f10,plain,(
% 0.19/0.50    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.19/0.50    inference(negated_conjecture,[],[f8])).
% 0.19/0.50  fof(f8,conjecture,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).
% 0.19/0.50  fof(f254,plain,(
% 0.19/0.50    ~r2_hidden(sK1,sK0) | (spl7_1 | ~spl7_12 | spl7_18)),
% 0.19/0.50    inference(forward_demodulation,[],[f241,f74])).
% 0.19/0.50  fof(f74,plain,(
% 0.19/0.50    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f57,f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.50    inference(equality_resolution,[],[f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.19/0.50  fof(f241,plain,(
% 0.19/0.50    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | (spl7_1 | ~spl7_12 | spl7_18)),
% 0.19/0.50    inference(backward_demodulation,[],[f60,f239])).
% 0.19/0.50  fof(f239,plain,(
% 0.19/0.50    k1_xboole_0 = sK2 | (~spl7_12 | spl7_18)),
% 0.19/0.50    inference(subsumption_resolution,[],[f238,f227])).
% 0.19/0.50  fof(f227,plain,(
% 0.19/0.50    ~r2_hidden(sK1,k1_setfam_1(sK2)) | spl7_18),
% 0.19/0.50    inference(avatar_component_clause,[],[f154])).
% 0.19/0.50  fof(f154,plain,(
% 0.19/0.50    spl7_18 <=> r2_hidden(sK1,k1_setfam_1(sK2))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.19/0.50  fof(f238,plain,(
% 0.19/0.50    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl7_12),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f237])).
% 0.19/0.50  fof(f237,plain,(
% 0.19/0.50    r2_hidden(sK1,k1_setfam_1(sK2)) | r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl7_12),
% 0.19/0.50    inference(resolution,[],[f108,f54])).
% 0.19/0.50  fof(f54,plain,(
% 0.19/0.50    ( ! [X0,X5] : (~r2_hidden(X5,sK6(X0,X5)) | r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(equality_resolution,[],[f39])).
% 0.19/0.50  fof(f39,plain,(
% 0.19/0.50    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK6(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1))))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ! [X1,X0] : (? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.19/0.50    inference(rectify,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.19/0.50    inference(nnf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.19/0.50  fof(f108,plain,(
% 0.19/0.50    ( ! [X0] : (r2_hidden(sK1,sK6(sK2,X0)) | r2_hidden(X0,k1_setfam_1(sK2))) ) | ~spl7_12),
% 0.19/0.50    inference(avatar_component_clause,[],[f107])).
% 0.19/0.50  fof(f107,plain,(
% 0.19/0.50    spl7_12 <=> ! [X0] : (r2_hidden(X0,k1_setfam_1(sK2)) | r2_hidden(sK1,sK6(sK2,X0)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.19/0.50  fof(f60,plain,(
% 0.19/0.50    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | spl7_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f59])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    spl7_1 <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.19/0.50  fof(f228,plain,(
% 0.19/0.50    spl7_11 | ~spl7_18 | spl7_1),
% 0.19/0.50    inference(avatar_split_clause,[],[f226,f59,f154,f104])).
% 0.19/0.50  fof(f104,plain,(
% 0.19/0.50    spl7_11 <=> k1_xboole_0 = sK2),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.19/0.50  fof(f226,plain,(
% 0.19/0.50    ~r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | spl7_1),
% 0.19/0.50    inference(subsumption_resolution,[],[f198,f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.50    inference(cnf_transformation,[],[f23])).
% 0.19/0.50  fof(f198,plain,(
% 0.19/0.50    ~r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl7_1),
% 0.19/0.50    inference(superposition,[],[f60,f116])).
% 0.19/0.50  fof(f116,plain,(
% 0.19/0.50    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f113])).
% 0.19/0.50  fof(f113,plain,(
% 0.19/0.50    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.19/0.50    inference(superposition,[],[f46,f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.50    inference(ennf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f197,plain,(
% 0.19/0.50    spl7_2 | ~spl7_3 | ~spl7_4),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f196])).
% 0.19/0.50  fof(f196,plain,(
% 0.19/0.50    $false | (spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.19/0.50    inference(subsumption_resolution,[],[f193,f63])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    ~r2_hidden(sK1,sK3) | spl7_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f62])).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    spl7_2 <=> r2_hidden(sK1,sK3)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.19/0.50  fof(f193,plain,(
% 0.19/0.50    r2_hidden(sK1,sK3) | (~spl7_3 | ~spl7_4)),
% 0.19/0.50    inference(resolution,[],[f72,f67])).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    r2_hidden(sK3,sK2) | ~spl7_3),
% 0.19/0.50    inference(avatar_component_clause,[],[f66])).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    spl7_3 <=> r2_hidden(sK3,sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.19/0.50  fof(f72,plain,(
% 0.19/0.50    ( ! [X4] : (~r2_hidden(X4,sK2) | r2_hidden(sK1,X4)) ) | ~spl7_4),
% 0.19/0.50    inference(avatar_component_clause,[],[f71])).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    spl7_4 <=> ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.19/0.50  fof(f192,plain,(
% 0.19/0.50    spl7_11 | spl7_4 | ~spl7_18),
% 0.19/0.50    inference(avatar_split_clause,[],[f191,f154,f71,f104])).
% 0.19/0.50  fof(f191,plain,(
% 0.19/0.50    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(sK1,X0) | k1_xboole_0 = sK2) ) | ~spl7_18),
% 0.19/0.50    inference(resolution,[],[f155,f56])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ( ! [X0,X7,X5] : (~r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X7,X0) | r2_hidden(X5,X7) | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(equality_resolution,[],[f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f29])).
% 0.19/0.50  fof(f155,plain,(
% 0.19/0.50    r2_hidden(sK1,k1_setfam_1(sK2)) | ~spl7_18),
% 0.19/0.50    inference(avatar_component_clause,[],[f154])).
% 0.19/0.50  fof(f183,plain,(
% 0.19/0.50    ~spl7_8),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f182])).
% 0.19/0.50  fof(f182,plain,(
% 0.19/0.50    $false | ~spl7_8),
% 0.19/0.50    inference(resolution,[],[f89,f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    v1_xboole_0(k1_xboole_0)),
% 0.19/0.50    inference(cnf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    v1_xboole_0(k1_xboole_0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.50  fof(f89,plain,(
% 0.19/0.50    ( ! [X1] : (~v1_xboole_0(X1)) ) | ~spl7_8),
% 0.19/0.50    inference(avatar_component_clause,[],[f88])).
% 0.19/0.50  fof(f88,plain,(
% 0.19/0.50    spl7_8 <=> ! [X1] : ~v1_xboole_0(X1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.19/0.50  fof(f178,plain,(
% 0.19/0.50    spl7_1 | ~spl7_11),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f177])).
% 0.19/0.50  fof(f177,plain,(
% 0.19/0.50    $false | (spl7_1 | ~spl7_11)),
% 0.19/0.50    inference(subsumption_resolution,[],[f176,f31])).
% 0.19/0.50  fof(f176,plain,(
% 0.19/0.50    ~r2_hidden(sK1,sK0) | (spl7_1 | ~spl7_11)),
% 0.19/0.50    inference(forward_demodulation,[],[f175,f74])).
% 0.19/0.50  fof(f175,plain,(
% 0.19/0.50    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | (spl7_1 | ~spl7_11)),
% 0.19/0.50    inference(forward_demodulation,[],[f60,f105])).
% 0.19/0.50  fof(f105,plain,(
% 0.19/0.50    k1_xboole_0 = sK2 | ~spl7_11),
% 0.19/0.50    inference(avatar_component_clause,[],[f104])).
% 0.19/0.50  fof(f167,plain,(
% 0.19/0.50    ~spl7_3 | ~spl7_7 | ~spl7_11),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f166])).
% 0.19/0.50  fof(f166,plain,(
% 0.19/0.50    $false | (~spl7_3 | ~spl7_7 | ~spl7_11)),
% 0.19/0.50    inference(subsumption_resolution,[],[f158,f86])).
% 0.19/0.50  fof(f86,plain,(
% 0.19/0.50    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl7_7),
% 0.19/0.50    inference(avatar_component_clause,[],[f85])).
% 0.19/0.50  fof(f85,plain,(
% 0.19/0.50    spl7_7 <=> ! [X2] : ~r2_hidden(X2,k1_xboole_0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.19/0.50  fof(f158,plain,(
% 0.19/0.50    r2_hidden(sK3,k1_xboole_0) | (~spl7_3 | ~spl7_11)),
% 0.19/0.50    inference(backward_demodulation,[],[f67,f105])).
% 0.19/0.50  fof(f156,plain,(
% 0.19/0.50    spl7_11 | spl7_18 | ~spl7_1),
% 0.19/0.50    inference(avatar_split_clause,[],[f152,f59,f154,f104])).
% 0.19/0.50  fof(f152,plain,(
% 0.19/0.50    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl7_1),
% 0.19/0.50    inference(subsumption_resolution,[],[f151,f30])).
% 0.19/0.50  fof(f151,plain,(
% 0.19/0.50    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl7_1),
% 0.19/0.50    inference(superposition,[],[f69,f116])).
% 0.19/0.50  fof(f69,plain,(
% 0.19/0.50    r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | ~spl7_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f59])).
% 0.19/0.50  fof(f109,plain,(
% 0.19/0.50    spl7_11 | spl7_12 | ~spl7_4),
% 0.19/0.50    inference(avatar_split_clause,[],[f102,f71,f107,f104])).
% 0.19/0.50  fof(f102,plain,(
% 0.19/0.50    ( ! [X0] : (r2_hidden(X0,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | r2_hidden(sK1,sK6(sK2,X0))) ) | ~spl7_4),
% 0.19/0.50    inference(resolution,[],[f55,f72])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),X0) | r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(equality_resolution,[],[f38])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK6(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f29])).
% 0.19/0.50  fof(f90,plain,(
% 0.19/0.50    spl7_7 | spl7_8),
% 0.19/0.50    inference(avatar_split_clause,[],[f76,f88,f85])).
% 0.19/0.50  fof(f76,plain,(
% 0.19/0.50    ( ! [X2,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.19/0.50    inference(resolution,[],[f49,f36])).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.19/0.50  fof(f73,plain,(
% 0.19/0.50    spl7_1 | spl7_4),
% 0.19/0.50    inference(avatar_split_clause,[],[f32,f71,f59])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ( ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f23])).
% 0.19/0.50  fof(f68,plain,(
% 0.19/0.50    ~spl7_1 | spl7_3),
% 0.19/0.50    inference(avatar_split_clause,[],[f33,f66,f59])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    r2_hidden(sK3,sK2) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.19/0.50    inference(cnf_transformation,[],[f23])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    ~spl7_1 | ~spl7_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f34,f62,f59])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.19/0.50    inference(cnf_transformation,[],[f23])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (7858)------------------------------
% 0.19/0.50  % (7858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (7858)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (7858)Memory used [KB]: 10746
% 0.19/0.50  % (7858)Time elapsed: 0.095 s
% 0.19/0.50  % (7858)------------------------------
% 0.19/0.50  % (7858)------------------------------
% 0.19/0.50  % (7873)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.51  % (7865)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.51  % (7862)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.51  % (7866)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.51  % (7870)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.51  % (7867)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.51  % (7850)Success in time 0.158 s
%------------------------------------------------------------------------------
