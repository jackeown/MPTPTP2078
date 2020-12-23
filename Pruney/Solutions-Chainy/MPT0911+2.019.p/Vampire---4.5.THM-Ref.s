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
% DateTime   : Thu Dec  3 12:59:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 318 expanded)
%              Number of leaves         :   23 (  87 expanded)
%              Depth                    :   21
%              Number of atoms          :  471 (1727 expanded)
%              Number of equality atoms :  198 ( 875 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f460,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f230,f271,f387,f400,f438,f457])).

% (20442)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f457,plain,
    ( ~ spl7_10
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f456])).

fof(f456,plain,
    ( $false
    | ~ spl7_10
    | spl7_12 ),
    inference(subsumption_resolution,[],[f452,f253])).

fof(f253,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl7_12
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f452,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_10 ),
    inference(resolution,[],[f446,f77])).

fof(f77,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f41,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f31])).

fof(f31,plain,
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f446,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f443,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f443,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
    | ~ spl7_10 ),
    inference(resolution,[],[f229,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f229,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl7_10
  <=> ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f438,plain,(
    ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f436,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f436,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f435,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f435,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f434,f45])).

fof(f45,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f434,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f433,f77])).

fof(f433,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f432,f223])).

fof(f223,plain,
    ( sK3 = k2_mcart_1(sK4)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl7_8
  <=> sK3 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f432,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f46,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f67,f61])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f46,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f400,plain,
    ( ~ spl7_9
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl7_9
    | spl7_12 ),
    inference(subsumption_resolution,[],[f395,f253])).

fof(f395,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_9 ),
    inference(resolution,[],[f366,f77])).

fof(f366,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) )
    | ~ spl7_9 ),
    inference(resolution,[],[f362,f57])).

fof(f362,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
    | ~ spl7_9 ),
    inference(resolution,[],[f226,f63])).

fof(f226,plain,
    ( ! [X1] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl7_9
  <=> ! [X1] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f387,plain,(
    ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f385,f43])).

fof(f385,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f384,f44])).

fof(f384,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f383,f45])).

fof(f383,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_12 ),
    inference(condensation,[],[f382])).

fof(f382,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f379,f98])).

fof(f98,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(resolution,[],[f96,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f37])).

fof(f37,plain,(
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

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f96,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f63,f91])).

fof(f91,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f59,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f379,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_12 ),
    inference(superposition,[],[f86,f371])).

fof(f371,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_12 ),
    inference(resolution,[],[f341,f50])).

fof(f341,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_12 ),
    inference(resolution,[],[f254,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
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

fof(f254,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f252])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f69,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f68,f61])).

% (20424)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f68,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f271,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f269,f43])).

fof(f269,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f268,f44])).

fof(f268,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f267,f45])).

fof(f267,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_7 ),
    inference(condensation,[],[f266])).

fof(f266,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f260,f98])).

fof(f260,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_7 ),
    inference(superposition,[],[f86,f244])).

fof(f244,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f235,f50])).

fof(f235,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_7 ),
    inference(resolution,[],[f233,f77])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X0,sK2))
        | ~ r2_hidden(X1,k2_zfmisc_1(X0,sK2)) )
    | ~ spl7_7 ),
    inference(resolution,[],[f231,f48])).

fof(f231,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_zfmisc_1(X0,sK2))
        | ~ m1_subset_1(sK4,k2_zfmisc_1(X0,sK2)) )
    | ~ spl7_7 ),
    inference(resolution,[],[f219,f57])).

fof(f219,plain,
    ( ! [X2] : ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl7_7
  <=> ! [X2] : ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f230,plain,
    ( spl7_7
    | spl7_8
    | spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f216,f228,f225,f221,f218])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))
      | sK3 = k2_mcart_1(sK4)
      | ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2)) ) ),
    inference(equality_resolution,[],[f215])).

fof(f215,plain,(
    ! [X2,X0,X5,X1] :
      ( sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X5,sK2)) ) ),
    inference(condensation,[],[f213])).

fof(f213,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X4))
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X5,sK2)) ) ),
    inference(resolution,[],[f212,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f212,plain,(
    ! [X6,X4,X0,X5,X3] :
      ( ~ v1_relat_1(X5)
      | sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4))
      | ~ r2_hidden(X0,X5)
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X6,sK2)) ) ),
    inference(condensation,[],[f210])).

fof(f210,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,X2))
      | k2_mcart_1(X0) = sK3
      | sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4))
      | ~ r2_hidden(X0,X5)
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(X0,k2_zfmisc_1(X6,sK2)) ) ),
    inference(resolution,[],[f180,f54])).

fof(f180,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k1_mcart_1(X1),X0)
      | sK3 = k2_mcart_1(X1)
      | sK4 != X1
      | ~ r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(sK0,X3))
      | ~ r2_hidden(X1,X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X1,k2_zfmisc_1(X5,sK2)) ) ),
    inference(resolution,[],[f178,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f178,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k1_mcart_1(X0),X1)
      | k2_mcart_1(X0) = sK3
      | sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3))
      | ~ r2_hidden(X0,X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f152,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f152,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK4 != k4_tarski(X0,X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | sK3 = X2
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,sK1))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,X4)) ) ),
    inference(resolution,[],[f142,f63])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X1),sK0)
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,k2_zfmisc_1(X3,sK1)) ) ),
    inference(resolution,[],[f141,f64])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK1)
      | sK3 = X1
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2)
      | k4_tarski(X0,X1) != sK4
      | ~ r2_hidden(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f140,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k2_mcart_1(X1),sK1)
      | ~ r2_hidden(k1_mcart_1(X1),sK0) ) ),
    inference(resolution,[],[f139,f58])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_mcart_1(X1),sK0)
      | ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k2_mcart_1(X1),sK1) ) ),
    inference(resolution,[],[f138,f58])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | sK3 = X1
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f76,f56])).

fof(f76,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f42,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:38:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (20426)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (20441)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (20426)Refutation not found, incomplete strategy% (20426)------------------------------
% 0.21/0.51  % (20426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20430)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (20421)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (20432)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (20426)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20426)Memory used [KB]: 10746
% 0.21/0.51  % (20426)Time elapsed: 0.093 s
% 0.21/0.51  % (20426)------------------------------
% 0.21/0.51  % (20426)------------------------------
% 0.21/0.52  % (20441)Refutation not found, incomplete strategy% (20441)------------------------------
% 0.21/0.52  % (20441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20418)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (20441)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20441)Memory used [KB]: 1791
% 0.21/0.52  % (20441)Time elapsed: 0.105 s
% 0.21/0.52  % (20441)------------------------------
% 0.21/0.52  % (20441)------------------------------
% 0.21/0.52  % (20440)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (20418)Refutation not found, incomplete strategy% (20418)------------------------------
% 0.21/0.52  % (20418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20418)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20418)Memory used [KB]: 1791
% 0.21/0.52  % (20418)Time elapsed: 0.110 s
% 0.21/0.52  % (20418)------------------------------
% 0.21/0.52  % (20418)------------------------------
% 0.21/0.52  % (20423)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (20419)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (20420)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (20422)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (20420)Refutation not found, incomplete strategy% (20420)------------------------------
% 0.21/0.53  % (20420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20420)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20420)Memory used [KB]: 10746
% 0.21/0.53  % (20420)Time elapsed: 0.125 s
% 0.21/0.53  % (20420)------------------------------
% 0.21/0.53  % (20420)------------------------------
% 0.21/0.53  % (20429)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (20433)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (20428)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (20435)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (20428)Refutation not found, incomplete strategy% (20428)------------------------------
% 0.21/0.54  % (20428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20428)Memory used [KB]: 10618
% 0.21/0.54  % (20428)Time elapsed: 0.125 s
% 0.21/0.54  % (20428)------------------------------
% 0.21/0.54  % (20428)------------------------------
% 0.21/0.54  % (20435)Refutation not found, incomplete strategy% (20435)------------------------------
% 0.21/0.54  % (20435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20435)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20435)Memory used [KB]: 10618
% 0.21/0.54  % (20435)Time elapsed: 0.134 s
% 0.21/0.54  % (20435)------------------------------
% 0.21/0.54  % (20435)------------------------------
% 0.21/0.54  % (20427)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (20438)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (20439)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (20445)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (20440)Refutation not found, incomplete strategy% (20440)------------------------------
% 0.21/0.54  % (20440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20440)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20440)Memory used [KB]: 10746
% 0.21/0.54  % (20440)Time elapsed: 0.082 s
% 0.21/0.54  % (20440)------------------------------
% 0.21/0.54  % (20440)------------------------------
% 0.21/0.54  % (20446)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (20431)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (20447)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (20444)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (20436)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (20434)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (20437)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (20425)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (20443)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (20427)Refutation not found, incomplete strategy% (20427)------------------------------
% 0.21/0.56  % (20427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20427)Memory used [KB]: 10746
% 0.21/0.56  % (20427)Time elapsed: 0.135 s
% 0.21/0.56  % (20427)------------------------------
% 0.21/0.56  % (20427)------------------------------
% 0.21/0.56  % (20421)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f460,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f230,f271,f387,f400,f438,f457])).
% 0.21/0.56  % (20442)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  fof(f457,plain,(
% 0.21/0.56    ~spl7_10 | spl7_12),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f456])).
% 0.21/0.56  fof(f456,plain,(
% 0.21/0.56    $false | (~spl7_10 | spl7_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f452,f253])).
% 0.21/0.56  fof(f253,plain,(
% 0.21/0.56    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl7_12),
% 0.21/0.56    inference(avatar_component_clause,[],[f252])).
% 0.21/0.56  fof(f252,plain,(
% 0.21/0.56    spl7_12 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.56  fof(f452,plain,(
% 0.21/0.56    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_10),
% 0.21/0.56    inference(resolution,[],[f446,f77])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.56    inference(definition_unfolding,[],[f41,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.56    inference(flattening,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.56    inference(negated_conjecture,[],[f18])).
% 0.21/0.56  fof(f18,conjecture,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.21/0.56  fof(f446,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl7_10),
% 0.21/0.56    inference(resolution,[],[f443,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.56  fof(f443,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl7_10),
% 0.21/0.56    inference(resolution,[],[f229,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.64/0.56  fof(f229,plain,(
% 1.64/0.56    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))) ) | ~spl7_10),
% 1.64/0.56    inference(avatar_component_clause,[],[f228])).
% 1.64/0.56  fof(f228,plain,(
% 1.64/0.56    spl7_10 <=> ! [X0] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))),
% 1.64/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.64/0.56  fof(f438,plain,(
% 1.64/0.56    ~spl7_8),
% 1.64/0.56    inference(avatar_contradiction_clause,[],[f437])).
% 1.64/0.56  fof(f437,plain,(
% 1.64/0.56    $false | ~spl7_8),
% 1.64/0.56    inference(subsumption_resolution,[],[f436,f43])).
% 1.64/0.56  fof(f43,plain,(
% 1.64/0.56    k1_xboole_0 != sK0),
% 1.64/0.56    inference(cnf_transformation,[],[f32])).
% 1.64/0.56  fof(f436,plain,(
% 1.64/0.56    k1_xboole_0 = sK0 | ~spl7_8),
% 1.64/0.56    inference(subsumption_resolution,[],[f435,f44])).
% 1.64/0.56  fof(f44,plain,(
% 1.64/0.56    k1_xboole_0 != sK1),
% 1.64/0.56    inference(cnf_transformation,[],[f32])).
% 1.64/0.56  fof(f435,plain,(
% 1.64/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_8),
% 1.64/0.56    inference(subsumption_resolution,[],[f434,f45])).
% 1.64/0.56  fof(f45,plain,(
% 1.64/0.56    k1_xboole_0 != sK2),
% 1.64/0.56    inference(cnf_transformation,[],[f32])).
% 1.64/0.56  fof(f434,plain,(
% 1.64/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_8),
% 1.64/0.56    inference(subsumption_resolution,[],[f433,f77])).
% 1.64/0.56  fof(f433,plain,(
% 1.64/0.56    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_8),
% 1.64/0.56    inference(subsumption_resolution,[],[f432,f223])).
% 1.64/0.56  fof(f223,plain,(
% 1.64/0.56    sK3 = k2_mcart_1(sK4) | ~spl7_8),
% 1.64/0.56    inference(avatar_component_clause,[],[f221])).
% 1.64/0.56  fof(f221,plain,(
% 1.64/0.56    spl7_8 <=> sK3 = k2_mcart_1(sK4)),
% 1.64/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.64/0.56  fof(f432,plain,(
% 1.64/0.56    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.64/0.56    inference(superposition,[],[f46,f79])).
% 1.64/0.56  fof(f79,plain,(
% 1.64/0.56    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.56    inference(definition_unfolding,[],[f67,f61])).
% 1.64/0.56  fof(f67,plain,(
% 1.64/0.56    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.56    inference(cnf_transformation,[],[f30])).
% 1.64/0.56  fof(f30,plain,(
% 1.64/0.56    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.64/0.56    inference(ennf_transformation,[],[f16])).
% 1.64/0.56  fof(f16,axiom,(
% 1.64/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.64/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.64/0.56  fof(f46,plain,(
% 1.64/0.56    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.64/0.56    inference(cnf_transformation,[],[f32])).
% 1.64/0.56  fof(f400,plain,(
% 1.64/0.56    ~spl7_9 | spl7_12),
% 1.64/0.56    inference(avatar_contradiction_clause,[],[f399])).
% 1.64/0.56  fof(f399,plain,(
% 1.64/0.56    $false | (~spl7_9 | spl7_12)),
% 1.64/0.56    inference(subsumption_resolution,[],[f395,f253])).
% 1.64/0.56  fof(f395,plain,(
% 1.64/0.56    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_9),
% 1.64/0.56    inference(resolution,[],[f366,f77])).
% 1.64/0.56  fof(f366,plain,(
% 1.64/0.56    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl7_9),
% 1.64/0.56    inference(resolution,[],[f362,f57])).
% 1.64/0.56  fof(f362,plain,(
% 1.64/0.56    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl7_9),
% 1.64/0.56    inference(resolution,[],[f226,f63])).
% 1.64/0.56  fof(f226,plain,(
% 1.64/0.56    ( ! [X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))) ) | ~spl7_9),
% 1.64/0.56    inference(avatar_component_clause,[],[f225])).
% 1.64/0.56  fof(f225,plain,(
% 1.64/0.56    spl7_9 <=> ! [X1] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))),
% 1.64/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.64/0.56  fof(f387,plain,(
% 1.64/0.56    ~spl7_12),
% 1.64/0.56    inference(avatar_contradiction_clause,[],[f386])).
% 1.64/0.56  fof(f386,plain,(
% 1.64/0.56    $false | ~spl7_12),
% 1.64/0.56    inference(subsumption_resolution,[],[f385,f43])).
% 1.64/0.56  fof(f385,plain,(
% 1.64/0.56    k1_xboole_0 = sK0 | ~spl7_12),
% 1.64/0.56    inference(subsumption_resolution,[],[f384,f44])).
% 1.64/0.56  fof(f384,plain,(
% 1.64/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_12),
% 1.64/0.56    inference(subsumption_resolution,[],[f383,f45])).
% 1.64/0.56  fof(f383,plain,(
% 1.64/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_12),
% 1.64/0.56    inference(condensation,[],[f382])).
% 1.64/0.56  fof(f382,plain,(
% 1.64/0.56    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_12),
% 1.64/0.56    inference(subsumption_resolution,[],[f379,f98])).
% 1.64/0.56  fof(f98,plain,(
% 1.64/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.64/0.56    inference(resolution,[],[f96,f50])).
% 1.64/0.56  fof(f50,plain,(
% 1.64/0.56    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.64/0.56    inference(cnf_transformation,[],[f38])).
% 1.64/0.56  fof(f38,plain,(
% 1.64/0.56    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 1.64/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f37])).
% 1.64/0.56  fof(f37,plain,(
% 1.64/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 1.64/0.56    introduced(choice_axiom,[])).
% 1.64/0.56  fof(f22,plain,(
% 1.64/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.64/0.56    inference(ennf_transformation,[],[f15])).
% 1.64/0.56  fof(f15,axiom,(
% 1.64/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.64/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 1.64/0.56  fof(f96,plain,(
% 1.64/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 1.64/0.56    inference(resolution,[],[f63,f91])).
% 1.64/0.56  fof(f91,plain,(
% 1.64/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.64/0.56    inference(resolution,[],[f59,f47])).
% 1.64/0.56  fof(f47,plain,(
% 1.64/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.64/0.56    inference(cnf_transformation,[],[f2])).
% 1.64/0.56  fof(f2,axiom,(
% 1.64/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.64/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.64/0.56  fof(f59,plain,(
% 1.64/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.64/0.56    inference(cnf_transformation,[],[f28])).
% 1.64/0.56  fof(f28,plain,(
% 1.64/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.64/0.56    inference(ennf_transformation,[],[f9])).
% 1.64/0.56  fof(f9,axiom,(
% 1.64/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.64/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.64/0.56  fof(f379,plain,(
% 1.64/0.56    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_12),
% 1.64/0.56    inference(superposition,[],[f86,f371])).
% 1.64/0.56  fof(f371,plain,(
% 1.64/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_12),
% 1.64/0.56    inference(resolution,[],[f341,f50])).
% 1.64/0.56  fof(f341,plain,(
% 1.64/0.56    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ) | ~spl7_12),
% 1.64/0.56    inference(resolution,[],[f254,f48])).
% 1.64/0.56  fof(f48,plain,(
% 1.64/0.56    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.64/0.56    inference(cnf_transformation,[],[f36])).
% 1.64/0.56  fof(f36,plain,(
% 1.64/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.64/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 1.64/0.56  fof(f35,plain,(
% 1.64/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.64/0.56    introduced(choice_axiom,[])).
% 1.64/0.56  fof(f34,plain,(
% 1.64/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.64/0.56    inference(rectify,[],[f33])).
% 1.64/0.56  fof(f33,plain,(
% 1.64/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.64/0.56    inference(nnf_transformation,[],[f1])).
% 1.64/0.56  fof(f1,axiom,(
% 1.64/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.64/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.64/0.56  fof(f254,plain,(
% 1.64/0.56    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_12),
% 1.64/0.56    inference(avatar_component_clause,[],[f252])).
% 1.64/0.56  fof(f86,plain,(
% 1.64/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.56    inference(definition_unfolding,[],[f69,f75])).
% 1.64/0.56  fof(f75,plain,(
% 1.64/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.64/0.56    inference(definition_unfolding,[],[f68,f61])).
% 1.64/0.56  % (20424)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.64/0.56  fof(f68,plain,(
% 1.64/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.64/0.56    inference(cnf_transformation,[],[f12])).
% 1.64/0.56  fof(f12,axiom,(
% 1.64/0.56    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.64/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.64/0.56  fof(f69,plain,(
% 1.64/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.64/0.56    inference(cnf_transformation,[],[f40])).
% 1.64/0.56  fof(f40,plain,(
% 1.64/0.56    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.64/0.56    inference(flattening,[],[f39])).
% 1.64/0.56  fof(f39,plain,(
% 1.64/0.56    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.64/0.56    inference(nnf_transformation,[],[f17])).
% 1.64/0.56  fof(f17,axiom,(
% 1.64/0.56    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.64/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.64/0.56  fof(f271,plain,(
% 1.64/0.56    ~spl7_7),
% 1.64/0.56    inference(avatar_contradiction_clause,[],[f270])).
% 1.64/0.56  fof(f270,plain,(
% 1.64/0.56    $false | ~spl7_7),
% 1.64/0.56    inference(subsumption_resolution,[],[f269,f43])).
% 1.64/0.56  fof(f269,plain,(
% 1.64/0.56    k1_xboole_0 = sK0 | ~spl7_7),
% 1.64/0.56    inference(subsumption_resolution,[],[f268,f44])).
% 1.64/0.56  fof(f268,plain,(
% 1.64/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_7),
% 1.64/0.56    inference(subsumption_resolution,[],[f267,f45])).
% 1.64/0.56  fof(f267,plain,(
% 1.64/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_7),
% 1.64/0.56    inference(condensation,[],[f266])).
% 1.64/0.56  fof(f266,plain,(
% 1.64/0.56    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_7),
% 1.64/0.56    inference(subsumption_resolution,[],[f260,f98])).
% 1.64/0.56  fof(f260,plain,(
% 1.64/0.56    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_7),
% 1.64/0.56    inference(superposition,[],[f86,f244])).
% 1.64/0.56  fof(f244,plain,(
% 1.64/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_7),
% 1.64/0.56    inference(resolution,[],[f235,f50])).
% 1.64/0.56  fof(f235,plain,(
% 1.64/0.56    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ) | ~spl7_7),
% 1.64/0.56    inference(resolution,[],[f233,f77])).
% 1.64/0.56  fof(f233,plain,(
% 1.64/0.56    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(X0,sK2)) | ~r2_hidden(X1,k2_zfmisc_1(X0,sK2))) ) | ~spl7_7),
% 1.64/0.56    inference(resolution,[],[f231,f48])).
% 1.64/0.56  fof(f231,plain,(
% 1.64/0.56    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,sK2)) | ~m1_subset_1(sK4,k2_zfmisc_1(X0,sK2))) ) | ~spl7_7),
% 1.64/0.56    inference(resolution,[],[f219,f57])).
% 1.64/0.56  fof(f219,plain,(
% 1.64/0.56    ( ! [X2] : (~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))) ) | ~spl7_7),
% 1.64/0.56    inference(avatar_component_clause,[],[f218])).
% 1.64/0.56  fof(f218,plain,(
% 1.64/0.56    spl7_7 <=> ! [X2] : ~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))),
% 1.64/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.64/0.56  fof(f230,plain,(
% 1.64/0.56    spl7_7 | spl7_8 | spl7_9 | spl7_10),
% 1.64/0.56    inference(avatar_split_clause,[],[f216,f228,f225,f221,f218])).
% 1.64/0.56  fof(f216,plain,(
% 1.64/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1)) | sK3 = k2_mcart_1(sK4) | ~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))) )),
% 1.64/0.56    inference(equality_resolution,[],[f215])).
% 1.64/0.56  fof(f215,plain,(
% 1.64/0.56    ( ! [X2,X0,X5,X1] : (sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X5,sK2))) )),
% 1.64/0.56    inference(condensation,[],[f213])).
% 1.64/0.56  fof(f213,plain,(
% 1.64/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X0,k2_zfmisc_1(X3,X4)) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X5,sK2))) )),
% 1.64/0.56    inference(resolution,[],[f212,f54])).
% 1.64/0.56  fof(f54,plain,(
% 1.64/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.64/0.56    inference(cnf_transformation,[],[f8])).
% 1.64/0.56  fof(f8,axiom,(
% 1.64/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.64/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.64/0.56  fof(f212,plain,(
% 1.64/0.56    ( ! [X6,X4,X0,X5,X3] : (~v1_relat_1(X5) | sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4)) | ~r2_hidden(X0,X5) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X6,sK2))) )),
% 1.64/0.56    inference(condensation,[],[f210])).
% 1.64/0.56  fof(f210,plain,(
% 1.64/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,X2)) | k2_mcart_1(X0) = sK3 | sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4)) | ~r2_hidden(X0,X5) | ~v1_relat_1(X5) | ~r2_hidden(X0,k2_zfmisc_1(X6,sK2))) )),
% 1.64/0.56    inference(resolution,[],[f180,f54])).
% 1.64/0.56  fof(f180,plain,(
% 1.64/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k1_mcart_1(X1),X0) | sK3 = k2_mcart_1(X1) | sK4 != X1 | ~r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK1)) | ~r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(sK0,X3)) | ~r2_hidden(X1,X4) | ~v1_relat_1(X4) | ~r2_hidden(X1,k2_zfmisc_1(X5,sK2))) )),
% 1.64/0.56    inference(resolution,[],[f178,f64])).
% 1.64/0.56  fof(f64,plain,(
% 1.64/0.56    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.64/0.56    inference(cnf_transformation,[],[f29])).
% 1.64/0.56  fof(f178,plain,(
% 1.64/0.56    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK2) | ~v1_relat_1(X1) | ~r2_hidden(k1_mcart_1(X0),X1) | k2_mcart_1(X0) = sK3 | sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3)) | ~r2_hidden(X0,X4) | ~v1_relat_1(X4)) )),
% 1.64/0.56    inference(superposition,[],[f152,f56])).
% 1.64/0.56  fof(f56,plain,(
% 1.64/0.56    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 1.64/0.56    inference(cnf_transformation,[],[f24])).
% 1.64/0.56  fof(f24,plain,(
% 1.64/0.56    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.64/0.56    inference(flattening,[],[f23])).
% 1.64/0.56  fof(f23,plain,(
% 1.64/0.56    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.64/0.56    inference(ennf_transformation,[],[f14])).
% 1.64/0.56  fof(f14,axiom,(
% 1.64/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.64/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.64/0.56  fof(f152,plain,(
% 1.64/0.56    ( ! [X4,X2,X0,X3,X1] : (sK4 != k4_tarski(X0,X2) | ~v1_relat_1(X1) | ~r2_hidden(X0,X1) | sK3 = X2 | ~r2_hidden(X2,sK2) | ~r2_hidden(X0,k2_zfmisc_1(X3,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,X4))) )),
% 1.64/0.56    inference(resolution,[],[f142,f63])).
% 1.64/0.56  fof(f142,plain,(
% 1.64/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(X1),sK0) | ~r2_hidden(X1,X2) | ~v1_relat_1(X2) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X0,sK2) | ~r2_hidden(X1,k2_zfmisc_1(X3,sK1))) )),
% 1.64/0.56    inference(resolution,[],[f141,f64])).
% 1.64/0.56  fof(f141,plain,(
% 1.64/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k2_mcart_1(X0),sK1) | sK3 = X1 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2) | k4_tarski(X0,X1) != sK4 | ~r2_hidden(k1_mcart_1(X0),sK0) | ~r2_hidden(X1,sK2)) )),
% 1.64/0.56    inference(resolution,[],[f140,f58])).
% 1.64/0.56  fof(f58,plain,(
% 1.64/0.56    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.64/0.56    inference(cnf_transformation,[],[f27])).
% 1.64/0.56  fof(f27,plain,(
% 1.64/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.64/0.56    inference(ennf_transformation,[],[f6])).
% 1.64/0.56  fof(f6,axiom,(
% 1.64/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.64/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.64/0.56  fof(f140,plain,(
% 1.64/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X1,X2) | ~v1_relat_1(X2) | ~r2_hidden(k2_mcart_1(X1),sK1) | ~r2_hidden(k1_mcart_1(X1),sK0)) )),
% 1.64/0.56    inference(resolution,[],[f139,f58])).
% 1.64/0.56  fof(f139,plain,(
% 1.64/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(k1_mcart_1(X1),sK0) | ~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X1,X2) | ~v1_relat_1(X2) | ~r2_hidden(k2_mcart_1(X1),sK1)) )),
% 1.64/0.56    inference(resolution,[],[f138,f58])).
% 1.64/0.56  fof(f138,plain,(
% 1.64/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | sK3 = X1 | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(k1_mcart_1(X0),sK0) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 1.64/0.56    inference(superposition,[],[f76,f56])).
% 1.64/0.56  fof(f76,plain,(
% 1.64/0.56    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.64/0.56    inference(definition_unfolding,[],[f42,f60])).
% 1.64/0.56  fof(f60,plain,(
% 1.64/0.56    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.64/0.56    inference(cnf_transformation,[],[f10])).
% 1.64/0.56  fof(f10,axiom,(
% 1.64/0.56    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.64/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.64/0.56  fof(f42,plain,(
% 1.64/0.56    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.64/0.56    inference(cnf_transformation,[],[f32])).
% 1.64/0.56  % SZS output end Proof for theBenchmark
% 1.64/0.56  % (20421)------------------------------
% 1.64/0.56  % (20421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.56  % (20421)Termination reason: Refutation
% 1.64/0.56  
% 1.64/0.56  % (20421)Memory used [KB]: 10874
% 1.64/0.56  % (20421)Time elapsed: 0.153 s
% 1.64/0.56  % (20421)------------------------------
% 1.64/0.56  % (20421)------------------------------
% 1.64/0.56  % (20417)Success in time 0.205 s
%------------------------------------------------------------------------------
