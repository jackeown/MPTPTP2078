%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t58_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:25 EDT 2019

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 387 expanded)
%              Number of leaves         :   17 ( 132 expanded)
%              Depth                    :   16
%              Number of atoms          :  406 (2088 expanded)
%              Number of equality atoms :  156 ( 404 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f13157,f13173,f13214,f13243])).

fof(f13243,plain,(
    ~ spl9_470 ),
    inference(avatar_contradiction_clause,[],[f13242])).

fof(f13242,plain,
    ( $false
    | ~ spl9_470 ),
    inference(subsumption_resolution,[],[f13241,f135])).

fof(f135,plain,(
    ~ r2_hidden(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f134,f52])).

fof(f52,plain,(
    ~ m1_subset_1(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ m1_subset_1(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                    & k1_xboole_0 != X0
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_subset_1(k2_enumset1(sK1,X2,X3,X4),k1_zfmisc_1(sK0))
                  & k1_xboole_0 != sK0
                  & m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ m1_subset_1(k2_enumset1(X1,sK2,X3,X4),k1_zfmisc_1(X0))
                & k1_xboole_0 != X0
                & m1_subset_1(X4,X0) )
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X4,X0) )
          & m1_subset_1(X3,X0) )
     => ( ? [X4] :
            ( ~ m1_subset_1(k2_enumset1(X1,X2,sK3,X4),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X4,X0) )
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X4,X0) )
     => ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,sK4),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( k1_xboole_0 != X0
                     => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k1_xboole_0 != X0
                   => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',t58_subset_1)).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f57,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',t7_boole)).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',d2_subset_1)).

fof(f13241,plain,
    ( r2_hidden(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0))
    | ~ spl9_470 ),
    inference(resolution,[],[f13238,f80])).

fof(f80,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK7(X0,X1),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r1_tarski(sK7(X0,X1),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK7(X0,X1),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( r1_tarski(sK7(X0,X1),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',d1_zfmisc_1)).

fof(f13238,plain,
    ( r1_tarski(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ spl9_470 ),
    inference(subsumption_resolution,[],[f13232,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f13232,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | r1_tarski(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ spl9_470 ),
    inference(superposition,[],[f183,f13156])).

fof(f13156,plain,
    ( sK1 = sK6(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ spl9_470 ),
    inference(avatar_component_clause,[],[f13155])).

fof(f13155,plain,
    ( spl9_470
  <=> sK1 = sK6(k2_enumset1(sK1,sK2,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_470])])).

fof(f183,plain,(
    ! [X14] :
      ( ~ m1_subset_1(sK6(X14,sK0),sK0)
      | r1_tarski(X14,sK0) ) ),
    inference(resolution,[],[f163,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',d3_tarski)).

fof(f163,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f162,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f162,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f157,f69])).

fof(f157,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f153,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f30])).

fof(f153,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f125,f47])).

fof(f125,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,X4)
      | r2_hidden(X3,X4)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f56,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',t6_boole)).

fof(f13214,plain,(
    ~ spl9_468 ),
    inference(avatar_contradiction_clause,[],[f13213])).

fof(f13213,plain,
    ( $false
    | ~ spl9_468 ),
    inference(subsumption_resolution,[],[f13212,f135])).

fof(f13212,plain,
    ( r2_hidden(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0))
    | ~ spl9_468 ),
    inference(resolution,[],[f13209,f80])).

fof(f13209,plain,
    ( r1_tarski(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ spl9_468 ),
    inference(subsumption_resolution,[],[f13203,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f13203,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | r1_tarski(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ spl9_468 ),
    inference(superposition,[],[f183,f13150])).

fof(f13150,plain,
    ( sK3 = sK6(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ spl9_468 ),
    inference(avatar_component_clause,[],[f13149])).

fof(f13149,plain,
    ( spl9_468
  <=> sK3 = sK6(k2_enumset1(sK1,sK2,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_468])])).

fof(f13173,plain,(
    ~ spl9_466 ),
    inference(avatar_contradiction_clause,[],[f13172])).

fof(f13172,plain,
    ( $false
    | ~ spl9_466 ),
    inference(subsumption_resolution,[],[f13171,f135])).

fof(f13171,plain,
    ( r2_hidden(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0))
    | ~ spl9_466 ),
    inference(resolution,[],[f13168,f80])).

fof(f13168,plain,
    ( r1_tarski(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ spl9_466 ),
    inference(subsumption_resolution,[],[f13162,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f13162,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r1_tarski(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ spl9_466 ),
    inference(superposition,[],[f183,f13144])).

fof(f13144,plain,
    ( sK2 = sK6(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ spl9_466 ),
    inference(avatar_component_clause,[],[f13143])).

fof(f13143,plain,
    ( spl9_466
  <=> sK2 = sK6(k2_enumset1(sK1,sK2,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_466])])).

fof(f13157,plain,
    ( spl9_466
    | spl9_468
    | spl9_470 ),
    inference(avatar_split_clause,[],[f13134,f13155,f13149,f13143])).

fof(f13134,plain,
    ( sK1 = sK6(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | sK3 = sK6(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | sK2 = sK6(k2_enumset1(sK1,sK2,sK3,sK4),sK0) ),
    inference(resolution,[],[f12617,f135])).

fof(f12617,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(k2_enumset1(X9,X10,X11,sK4),k1_zfmisc_1(sK0))
      | sK6(k2_enumset1(X9,X10,X11,sK4),sK0) = X9
      | sK6(k2_enumset1(X9,X10,X11,sK4),sK0) = X11
      | sK6(k2_enumset1(X9,X10,X11,sK4),sK0) = X10 ) ),
    inference(resolution,[],[f9184,f50])).

fof(f50,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f9184,plain,(
    ! [X30,X28,X29,X27] :
      ( ~ m1_subset_1(X30,sK0)
      | sK6(k2_enumset1(X27,X28,X29,X30),sK0) = X28
      | sK6(k2_enumset1(X27,X28,X29,X30),sK0) = X27
      | sK6(k2_enumset1(X27,X28,X29,X30),sK0) = X29
      | r2_hidden(k2_enumset1(X27,X28,X29,X30),k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f9175,f80])).

fof(f9175,plain,(
    ! [X30,X28,X29,X27] :
      ( ~ m1_subset_1(X30,sK0)
      | r1_tarski(k2_enumset1(X27,X28,X29,X30),sK0)
      | sK6(k2_enumset1(X27,X28,X29,X30),sK0) = X28
      | sK6(k2_enumset1(X27,X28,X29,X30),sK0) = X27
      | sK6(k2_enumset1(X27,X28,X29,X30),sK0) = X29
      | r2_hidden(k2_enumset1(X27,X28,X29,X30),k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f183,f354])).

fof(f354,plain,(
    ! [X28,X26,X29,X27,X25] :
      ( sK6(k2_enumset1(X26,X27,X25,X28),X29) = X28
      | sK6(k2_enumset1(X26,X27,X25,X28),X29) = X27
      | sK6(k2_enumset1(X26,X27,X25,X28),X29) = X26
      | sK6(k2_enumset1(X26,X27,X25,X28),X29) = X25
      | r2_hidden(k2_enumset1(X26,X27,X25,X28),k1_zfmisc_1(X29)) ) ),
    inference(resolution,[],[f90,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f62,f80])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(X6,k2_enumset1(X0,X1,X2,X3))
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | X3 = X6 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X3 = X6
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | ~ r2_hidden(X6,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ( ( ( sK8(X0,X1,X2,X3,X4) != X3
              & sK8(X0,X1,X2,X3,X4) != X2
              & sK8(X0,X1,X2,X3,X4) != X1
              & sK8(X0,X1,X2,X3,X4) != X0 )
            | ~ r2_hidden(sK8(X0,X1,X2,X3,X4),X4) )
          & ( sK8(X0,X1,X2,X3,X4) = X3
            | sK8(X0,X1,X2,X3,X4) = X2
            | sK8(X0,X1,X2,X3,X4) = X1
            | sK8(X0,X1,X2,X3,X4) = X0
            | r2_hidden(sK8(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f44,f45])).

fof(f45,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK8(X0,X1,X2,X3,X4) != X3
            & sK8(X0,X1,X2,X3,X4) != X2
            & sK8(X0,X1,X2,X3,X4) != X1
            & sK8(X0,X1,X2,X3,X4) != X0 )
          | ~ r2_hidden(sK8(X0,X1,X2,X3,X4),X4) )
        & ( sK8(X0,X1,X2,X3,X4) = X3
          | sK8(X0,X1,X2,X3,X4) = X2
          | sK8(X0,X1,X2,X3,X4) = X1
          | sK8(X0,X1,X2,X3,X4) = X0
          | r2_hidden(sK8(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',d2_enumset1)).
%------------------------------------------------------------------------------
