%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 223 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  387 (1162 expanded)
%              Number of equality atoms :   89 ( 230 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f77,f106,f117,f132,f146,f151,f153,f188,f216])).

fof(f216,plain,
    ( spl7_1
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f214,f79])).

fof(f79,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f61,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f61,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f214,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | spl7_1
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f202,f54])).

fof(f54,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | k1_xboole_0 != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).

fof(f25,plain,(
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

% (4402)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK4(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK6(X0,X5))
        & r2_hidden(sK6(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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

fof(f202,plain,
    ( r2_hidden(sK1,k1_setfam_1(k1_xboole_0))
    | spl7_1
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f131,f191])).

fof(f191,plain,
    ( k1_xboole_0 = sK2
    | spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f190,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( ~ r2_hidden(sK1,sK3)
        & r2_hidden(sK3,sK2) )
      | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & ( ! [X4] :
          ( r2_hidden(sK1,X4)
          | ~ r2_hidden(X4,sK2) )
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & r2_hidden(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK1,X3)
        & r2_hidden(X3,sK2) )
   => ( ~ r2_hidden(sK1,sK3)
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f190,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f189,f131])).

fof(f189,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl7_1 ),
    inference(superposition,[],[f64,f126])).

fof(f126,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f64,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_1
  <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f131,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_9
  <=> r2_hidden(sK1,k1_setfam_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f188,plain,
    ( spl7_7
    | spl7_9
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f187,f63,f130,f101])).

fof(f101,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f187,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f186,f31])).

fof(f186,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_1 ),
    inference(superposition,[],[f73,f126])).

fof(f73,plain,
    ( r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f153,plain,
    ( spl7_7
    | spl7_4
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f152,f130,f75,f101])).

fof(f75,plain,
    ( spl7_4
  <=> ! [X4] :
        ( r2_hidden(sK1,X4)
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(sK1,X0)
        | k1_xboole_0 = sK2 )
    | ~ spl7_9 ),
    inference(resolution,[],[f131,f59])).

fof(f59,plain,(
    ! [X0,X7,X5] :
      ( ~ r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X7,X0)
      | r2_hidden(X5,X7)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f151,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f148,f67])).

fof(f67,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f148,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f76,f71])).

fof(f71,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f76,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | r2_hidden(sK1,X4) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f146,plain,
    ( ~ spl7_3
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f144,f79])).

fof(f144,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f71,f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f132,plain,
    ( spl7_7
    | spl7_9
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f128,f104,f130,f101])).

fof(f104,plain,
    ( spl7_8
  <=> ! [X6] :
        ( r2_hidden(X6,k1_setfam_1(sK2))
        | r2_hidden(sK1,sK6(sK2,X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f128,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_8 ),
    inference(resolution,[],[f105,f57])).

fof(f57,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,sK6(X0,X5))
      | r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK6(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f105,plain,
    ( ! [X6] :
        ( r2_hidden(sK1,sK6(sK2,X6))
        | r2_hidden(X6,k1_setfam_1(sK2)) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f117,plain,
    ( spl7_1
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f115,f32])).

fof(f32,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f115,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl7_1
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f108,f78])).

fof(f78,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f60,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f108,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl7_1
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f64,f102])).

fof(f106,plain,
    ( spl7_7
    | spl7_8
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f99,f75,f104,f101])).

fof(f99,plain,
    ( ! [X6] :
        ( r2_hidden(X6,k1_setfam_1(sK2))
        | k1_xboole_0 = sK2
        | r2_hidden(sK1,sK6(sK2,X6)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f58,f76])).

fof(f58,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),X0)
      | r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK6(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f33,f75,f63])).

fof(f33,plain,(
    ! [X4] :
      ( r2_hidden(sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f34,f70,f63])).

fof(f34,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f35,f66,f63])).

fof(f35,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:13:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (4396)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (4398)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (4401)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (4412)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (4411)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (4399)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (4406)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (4408)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (4398)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f68,f72,f77,f106,f117,f132,f146,f151,f153,f188,f216])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    spl7_1 | ~spl7_9),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f215])).
% 0.20/0.49  fof(f215,plain,(
% 0.20/0.49    $false | (spl7_1 | ~spl7_9)),
% 0.20/0.49    inference(subsumption_resolution,[],[f214,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(superposition,[],[f61,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.49    inference(equality_resolution,[],[f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.49    inference(flattening,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_xboole_0) | (spl7_1 | ~spl7_9)),
% 0.20/0.49    inference(forward_demodulation,[],[f202,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 0.20/0.49    inference(equality_resolution,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | k1_xboole_0 != X0) )),
% 0.20/0.49    inference(equality_resolution,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | k1_xboole_0 != X1 | k1_xboole_0 != X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  % (4402)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.20/0.49    inference(rectify,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_setfam_1(k1_xboole_0)) | (spl7_1 | ~spl7_9)),
% 0.20/0.49    inference(backward_demodulation,[],[f131,f191])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | (spl7_1 | ~spl7_9)),
% 0.20/0.49    inference(subsumption_resolution,[],[f190,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ((~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) => (~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(rectify,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(nnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f8])).
% 0.20/0.49  fof(f8,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl7_1 | ~spl7_9)),
% 0.20/0.49    inference(subsumption_resolution,[],[f189,f131])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl7_1),
% 0.20/0.49    inference(superposition,[],[f64,f126])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f123])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.20/0.49    inference(superposition,[],[f47,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | spl7_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    spl7_1 <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_setfam_1(sK2)) | ~spl7_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f130])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    spl7_9 <=> r2_hidden(sK1,k1_setfam_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    spl7_7 | spl7_9 | ~spl7_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f187,f63,f130,f101])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl7_7 <=> k1_xboole_0 = sK2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl7_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f186,f31])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl7_1),
% 0.20/0.49    inference(superposition,[],[f73,f126])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | ~spl7_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f63])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    spl7_7 | spl7_4 | ~spl7_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f152,f130,f75,f101])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl7_4 <=> ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(sK1,X0) | k1_xboole_0 = sK2) ) | ~spl7_9),
% 0.20/0.49    inference(resolution,[],[f131,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0,X7,X5] : (~r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X7,X0) | r2_hidden(X5,X7) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(equality_resolution,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    spl7_2 | ~spl7_3 | ~spl7_4),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f150])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    $false | (spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f148,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ~r2_hidden(sK1,sK3) | spl7_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl7_2 <=> r2_hidden(sK1,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    r2_hidden(sK1,sK3) | (~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(resolution,[],[f76,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    r2_hidden(sK3,sK2) | ~spl7_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl7_3 <=> r2_hidden(sK3,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X4] : (~r2_hidden(X4,sK2) | r2_hidden(sK1,X4)) ) | ~spl7_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ~spl7_3 | ~spl7_7),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f145])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    $false | (~spl7_3 | ~spl7_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f144,f79])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    r2_hidden(sK3,k1_xboole_0) | (~spl7_3 | ~spl7_7)),
% 0.20/0.49    inference(forward_demodulation,[],[f71,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~spl7_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    spl7_7 | spl7_9 | ~spl7_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f128,f104,f130,f101])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    spl7_8 <=> ! [X6] : (r2_hidden(X6,k1_setfam_1(sK2)) | r2_hidden(sK1,sK6(sK2,X6)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl7_8),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f127])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_setfam_1(sK2)) | r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl7_8),
% 0.20/0.49    inference(resolution,[],[f105,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X5] : (~r2_hidden(X5,sK6(X0,X5)) | r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(equality_resolution,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK6(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X6] : (r2_hidden(sK1,sK6(sK2,X6)) | r2_hidden(X6,k1_setfam_1(sK2))) ) | ~spl7_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f104])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl7_1 | ~spl7_7),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    $false | (spl7_1 | ~spl7_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f115,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    r2_hidden(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ~r2_hidden(sK1,sK0) | (spl7_1 | ~spl7_7)),
% 0.20/0.49    inference(forward_demodulation,[],[f108,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f60,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.49    inference(equality_resolution,[],[f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | (spl7_1 | ~spl7_7)),
% 0.20/0.49    inference(backward_demodulation,[],[f64,f102])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    spl7_7 | spl7_8 | ~spl7_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f99,f75,f104,f101])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X6] : (r2_hidden(X6,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | r2_hidden(sK1,sK6(sK2,X6))) ) | ~spl7_4),
% 0.20/0.49    inference(resolution,[],[f58,f76])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),X0) | r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(equality_resolution,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK6(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl7_1 | spl7_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f75,f63])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ~spl7_1 | spl7_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f34,f70,f63])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    r2_hidden(sK3,sK2) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ~spl7_1 | ~spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f66,f63])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (4398)------------------------------
% 0.20/0.49  % (4398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4398)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (4398)Memory used [KB]: 10746
% 0.20/0.49  % (4398)Time elapsed: 0.068 s
% 0.20/0.49  % (4398)------------------------------
% 0.20/0.49  % (4398)------------------------------
% 0.20/0.49  % (4395)Success in time 0.13 s
%------------------------------------------------------------------------------
