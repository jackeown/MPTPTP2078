%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:33 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 323 expanded)
%              Number of leaves         :   32 ( 114 expanded)
%              Depth                    :   15
%              Number of atoms          :  533 (2160 expanded)
%              Number of equality atoms :  109 ( 589 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f87,f98,f107,f111,f113,f127,f143,f145,f154,f158,f163,f224,f232,f299])).

fof(f299,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_20 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f69,f291])).

fof(f291,plain,
    ( sK2 = sK3
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f260,f257])).

fof(f257,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_5
    | ~ spl7_20 ),
    inference(resolution,[],[f175,f81])).

fof(f81,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_5
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_20
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f260,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f256,f73])).

fof(f73,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_3
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f256,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(resolution,[],[f175,f77])).

fof(f77,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl7_4
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f69,plain,
    ( sK2 != sK3
    | spl7_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_2
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f232,plain,
    ( ~ spl7_1
    | spl7_20
    | spl7_21 ),
    inference(avatar_split_clause,[],[f231,f177,f174,f65])).

fof(f65,plain,
    ( spl7_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f177,plain,
    ( spl7_21
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f231,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v2_funct_1(sK1)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(global_subsumption,[],[f39,f40,f227])).

fof(f227,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v2_funct_1(sK1)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f41,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( sK2 != sK3
        & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,sK0)
        & r2_hidden(sK2,sK0) )
      | ~ v2_funct_1(sK1) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
          | ~ r2_hidden(X5,sK0)
          | ~ r2_hidden(X4,sK0) )
      | v2_funct_1(sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK0)
            & r2_hidden(X2,sK0) )
        | ~ v2_funct_1(sK1) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
            | ~ r2_hidden(X5,sK0)
            | ~ r2_hidden(X4,sK0) )
        | v2_funct_1(sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f40,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f224,plain,
    ( ~ spl7_4
    | ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(resolution,[],[f193,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f193,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(resolution,[],[f184,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f184,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(backward_demodulation,[],[f77,f178])).

fof(f178,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f177])).

fof(f163,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_1
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f162,f152,f65,f93,f90])).

fof(f90,plain,
    ( spl7_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f93,plain,
    ( spl7_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f152,plain,
    ( spl7_17
  <=> sK4(sK1) = sK5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f162,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_17 ),
    inference(trivial_inequality_removal,[],[f161])).

fof(f161,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_17 ),
    inference(superposition,[],[f53,f153])).

fof(f153,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f152])).

fof(f53,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f158,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_1
    | ~ spl7_15
    | spl7_16 ),
    inference(avatar_split_clause,[],[f156,f149,f141,f65,f93,f90])).

fof(f141,plain,
    ( spl7_15
  <=> r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f149,plain,
    ( spl7_16
  <=> r2_hidden(sK4(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f156,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_16 ),
    inference(resolution,[],[f155,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1),X0)
        | ~ r1_tarski(X0,sK0) )
    | spl7_16 ),
    inference(resolution,[],[f150,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f150,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f154,plain,
    ( ~ spl7_16
    | spl7_17
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f147,f124,f152,f149])).

fof(f124,plain,
    ( spl7_12
  <=> ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f147,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ r2_hidden(sK4(sK1),sK0)
    | ~ spl7_12 ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f145,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl7_15 ),
    inference(subsumption_resolution,[],[f129,f142])).

fof(f142,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f129,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f115,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f115,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(global_subsumption,[],[f41,f114])).

fof(f114,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f62,f100])).

fof(f100,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f41,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f143,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_1
    | ~ spl7_15
    | spl7_11 ),
    inference(avatar_split_clause,[],[f138,f121,f141,f65,f93,f90])).

fof(f121,plain,
    ( spl7_11
  <=> r2_hidden(sK5(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f138,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_11 ),
    inference(resolution,[],[f128,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1),X0)
        | ~ r1_tarski(X0,sK0) )
    | spl7_11 ),
    inference(resolution,[],[f122,f55])).

fof(f122,plain,
    ( ~ r2_hidden(sK5(sK1),sK0)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f127,plain,
    ( ~ spl7_11
    | spl7_12
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f117,f96,f85,f124,f121])).

fof(f85,plain,
    ( spl7_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f96,plain,
    ( spl7_9
  <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f117,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1))
        | ~ r2_hidden(sK5(sK1),sK0)
        | ~ r2_hidden(X1,sK0)
        | sK5(sK1) = X1 )
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(superposition,[],[f86,f97])).

fof(f97,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f86,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | X4 = X5 )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f113,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f39,f94])).

fof(f94,plain,
    ( ~ v1_funct_1(sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f111,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl7_10 ),
    inference(resolution,[],[f105,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f105,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_10
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f107,plain,
    ( ~ spl7_10
    | spl7_7 ),
    inference(avatar_split_clause,[],[f102,f90,f104])).

fof(f102,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f98,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | spl7_1 ),
    inference(avatar_split_clause,[],[f88,f65,f96,f93,f90])).

fof(f88,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_1 ),
    inference(resolution,[],[f66,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,
    ( ~ v2_funct_1(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f87,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f42,f85,f65])).

fof(f42,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f43,f80,f65])).

fof(f43,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f44,f76,f65])).

fof(f44,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f45,f72,f65])).

fof(f45,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f46,f68,f65])).

fof(f46,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:56:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (13560)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (13562)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.53  % (13556)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.53  % (13555)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.53  % (13564)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.53  % (13559)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.53  % (13557)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.53  % (13580)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.54  % (13577)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.54  % (13555)Refutation not found, incomplete strategy% (13555)------------------------------
% 1.38/0.54  % (13555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (13555)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (13555)Memory used [KB]: 1663
% 1.38/0.54  % (13555)Time elapsed: 0.126 s
% 1.38/0.54  % (13555)------------------------------
% 1.38/0.54  % (13555)------------------------------
% 1.38/0.54  % (13574)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.54  % (13572)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.54  % (13558)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.54  % (13568)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.54  % (13572)Refutation not found, incomplete strategy% (13572)------------------------------
% 1.38/0.54  % (13572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (13572)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (13572)Memory used [KB]: 10618
% 1.38/0.54  % (13572)Time elapsed: 0.093 s
% 1.38/0.54  % (13572)------------------------------
% 1.38/0.54  % (13572)------------------------------
% 1.38/0.54  % (13564)Refutation not found, incomplete strategy% (13564)------------------------------
% 1.38/0.54  % (13564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (13570)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.54  % (13567)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.55  % (13569)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.55  % (13576)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (13571)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.55  % (13564)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (13564)Memory used [KB]: 10618
% 1.38/0.55  % (13564)Time elapsed: 0.121 s
% 1.38/0.55  % (13564)------------------------------
% 1.38/0.55  % (13564)------------------------------
% 1.38/0.55  % (13565)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.55  % (13563)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.55  % (13565)Refutation not found, incomplete strategy% (13565)------------------------------
% 1.38/0.55  % (13565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (13565)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (13565)Memory used [KB]: 10618
% 1.38/0.55  % (13565)Time elapsed: 0.146 s
% 1.38/0.55  % (13565)------------------------------
% 1.38/0.55  % (13565)------------------------------
% 1.38/0.55  % (13584)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.55  % (13575)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  % (13561)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.55  % (13566)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.55  % (13578)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.55  % (13566)Refutation not found, incomplete strategy% (13566)------------------------------
% 1.38/0.55  % (13566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (13566)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (13566)Memory used [KB]: 10618
% 1.38/0.55  % (13566)Time elapsed: 0.147 s
% 1.38/0.55  % (13566)------------------------------
% 1.38/0.55  % (13566)------------------------------
% 1.38/0.56  % (13579)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.56  % (13573)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.56  % (13557)Refutation found. Thanks to Tanya!
% 1.38/0.56  % SZS status Theorem for theBenchmark
% 1.38/0.56  % SZS output start Proof for theBenchmark
% 1.38/0.56  fof(f300,plain,(
% 1.38/0.56    $false),
% 1.38/0.56    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f87,f98,f107,f111,f113,f127,f143,f145,f154,f158,f163,f224,f232,f299])).
% 1.38/0.56  fof(f299,plain,(
% 1.38/0.56    spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_20),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f292])).
% 1.38/0.56  fof(f292,plain,(
% 1.38/0.56    $false | (spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_20)),
% 1.38/0.56    inference(subsumption_resolution,[],[f69,f291])).
% 1.38/0.56  fof(f291,plain,(
% 1.38/0.56    sK2 = sK3 | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_20)),
% 1.38/0.56    inference(forward_demodulation,[],[f260,f257])).
% 1.38/0.56  fof(f257,plain,(
% 1.38/0.56    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_5 | ~spl7_20)),
% 1.38/0.56    inference(resolution,[],[f175,f81])).
% 1.38/0.56  fof(f81,plain,(
% 1.38/0.56    r2_hidden(sK2,sK0) | ~spl7_5),
% 1.38/0.56    inference(avatar_component_clause,[],[f80])).
% 1.38/0.56  fof(f80,plain,(
% 1.38/0.56    spl7_5 <=> r2_hidden(sK2,sK0)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.38/0.56  fof(f175,plain,(
% 1.38/0.56    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl7_20),
% 1.38/0.56    inference(avatar_component_clause,[],[f174])).
% 1.38/0.56  fof(f174,plain,(
% 1.38/0.56    spl7_20 <=> ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.38/0.56  fof(f260,plain,(
% 1.38/0.56    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_3 | ~spl7_4 | ~spl7_20)),
% 1.38/0.56    inference(forward_demodulation,[],[f256,f73])).
% 1.38/0.56  fof(f73,plain,(
% 1.38/0.56    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl7_3),
% 1.38/0.56    inference(avatar_component_clause,[],[f72])).
% 1.38/0.56  fof(f72,plain,(
% 1.38/0.56    spl7_3 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.38/0.56  fof(f256,plain,(
% 1.38/0.56    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl7_4 | ~spl7_20)),
% 1.38/0.56    inference(resolution,[],[f175,f77])).
% 1.38/0.56  fof(f77,plain,(
% 1.38/0.56    r2_hidden(sK3,sK0) | ~spl7_4),
% 1.38/0.56    inference(avatar_component_clause,[],[f76])).
% 1.38/0.56  fof(f76,plain,(
% 1.38/0.56    spl7_4 <=> r2_hidden(sK3,sK0)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.38/0.56  fof(f69,plain,(
% 1.38/0.56    sK2 != sK3 | spl7_2),
% 1.38/0.56    inference(avatar_component_clause,[],[f68])).
% 1.38/0.56  fof(f68,plain,(
% 1.38/0.56    spl7_2 <=> sK2 = sK3),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.38/0.56  fof(f232,plain,(
% 1.38/0.56    ~spl7_1 | spl7_20 | spl7_21),
% 1.38/0.56    inference(avatar_split_clause,[],[f231,f177,f174,f65])).
% 1.38/0.56  fof(f65,plain,(
% 1.38/0.56    spl7_1 <=> v2_funct_1(sK1)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.38/0.56  fof(f177,plain,(
% 1.38/0.56    spl7_21 <=> k1_xboole_0 = sK0),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.38/0.56  fof(f231,plain,(
% 1.38/0.56    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v2_funct_1(sK1) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 1.38/0.56    inference(global_subsumption,[],[f39,f40,f227])).
% 1.38/0.56  fof(f227,plain,(
% 1.38/0.56    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v2_funct_1(sK1) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.38/0.56    inference(resolution,[],[f41,f63])).
% 1.38/0.56  fof(f63,plain,(
% 1.38/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f23])).
% 1.38/0.56  fof(f23,plain,(
% 1.38/0.56    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.38/0.56    inference(flattening,[],[f22])).
% 1.38/0.56  fof(f22,plain,(
% 1.38/0.56    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.38/0.56    inference(ennf_transformation,[],[f10])).
% 1.38/0.56  fof(f10,axiom,(
% 1.38/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 1.38/0.56  fof(f41,plain,(
% 1.38/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.38/0.56    inference(cnf_transformation,[],[f29])).
% 1.38/0.56  fof(f29,plain,(
% 1.38/0.56    ((sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) | ~v2_funct_1(sK1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.38/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f28,f27])).
% 1.38/0.56  fof(f27,plain,(
% 1.38/0.56    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) | ~v2_funct_1(sK1)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f28,plain,(
% 1.38/0.56    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f26,plain,(
% 1.38/0.56    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.38/0.56    inference(rectify,[],[f25])).
% 1.38/0.56  fof(f25,plain,(
% 1.38/0.56    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.38/0.56    inference(flattening,[],[f24])).
% 1.38/0.56  fof(f24,plain,(
% 1.38/0.56    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.38/0.56    inference(nnf_transformation,[],[f14])).
% 1.38/0.56  fof(f14,plain,(
% 1.38/0.56    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.38/0.56    inference(flattening,[],[f13])).
% 1.38/0.56  fof(f13,plain,(
% 1.38/0.56    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.38/0.56    inference(ennf_transformation,[],[f12])).
% 1.38/0.56  fof(f12,negated_conjecture,(
% 1.38/0.56    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.38/0.56    inference(negated_conjecture,[],[f11])).
% 1.38/0.56  fof(f11,conjecture,(
% 1.38/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 1.38/0.56  fof(f40,plain,(
% 1.38/0.56    v1_funct_2(sK1,sK0,sK0)),
% 1.38/0.56    inference(cnf_transformation,[],[f29])).
% 1.38/0.56  fof(f39,plain,(
% 1.38/0.56    v1_funct_1(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f29])).
% 1.38/0.56  fof(f224,plain,(
% 1.38/0.56    ~spl7_4 | ~spl7_21),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f223])).
% 1.38/0.56  fof(f223,plain,(
% 1.38/0.56    $false | (~spl7_4 | ~spl7_21)),
% 1.38/0.56    inference(resolution,[],[f193,f47])).
% 1.38/0.56  fof(f47,plain,(
% 1.38/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f2])).
% 1.38/0.56  fof(f2,axiom,(
% 1.38/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.38/0.56  fof(f193,plain,(
% 1.38/0.56    ~r1_tarski(k1_xboole_0,sK3) | (~spl7_4 | ~spl7_21)),
% 1.38/0.56    inference(resolution,[],[f184,f60])).
% 1.38/0.56  fof(f60,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f19])).
% 1.38/0.56  fof(f19,plain,(
% 1.38/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f7])).
% 1.38/0.56  fof(f7,axiom,(
% 1.38/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.38/0.56  fof(f184,plain,(
% 1.38/0.56    r2_hidden(sK3,k1_xboole_0) | (~spl7_4 | ~spl7_21)),
% 1.38/0.56    inference(backward_demodulation,[],[f77,f178])).
% 1.38/0.56  fof(f178,plain,(
% 1.38/0.56    k1_xboole_0 = sK0 | ~spl7_21),
% 1.38/0.56    inference(avatar_component_clause,[],[f177])).
% 1.38/0.56  fof(f163,plain,(
% 1.38/0.56    ~spl7_7 | ~spl7_8 | spl7_1 | ~spl7_17),
% 1.38/0.56    inference(avatar_split_clause,[],[f162,f152,f65,f93,f90])).
% 1.38/0.56  fof(f90,plain,(
% 1.38/0.56    spl7_7 <=> v1_relat_1(sK1)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.38/0.56  fof(f93,plain,(
% 1.38/0.56    spl7_8 <=> v1_funct_1(sK1)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.38/0.56  fof(f152,plain,(
% 1.38/0.56    spl7_17 <=> sK4(sK1) = sK5(sK1)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.38/0.56  fof(f162,plain,(
% 1.38/0.56    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_17),
% 1.38/0.56    inference(trivial_inequality_removal,[],[f161])).
% 1.38/0.56  fof(f161,plain,(
% 1.38/0.56    sK4(sK1) != sK4(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_17),
% 1.38/0.56    inference(superposition,[],[f53,f153])).
% 1.38/0.56  fof(f153,plain,(
% 1.38/0.56    sK4(sK1) = sK5(sK1) | ~spl7_17),
% 1.38/0.56    inference(avatar_component_clause,[],[f152])).
% 1.38/0.56  fof(f53,plain,(
% 1.38/0.56    ( ! [X0] : (sK4(X0) != sK5(X0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f33])).
% 1.38/0.56  fof(f33,plain,(
% 1.38/0.56    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f32])).
% 1.38/0.56  fof(f32,plain,(
% 1.38/0.56    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f31,plain,(
% 1.38/0.56    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(rectify,[],[f30])).
% 1.38/0.56  fof(f30,plain,(
% 1.38/0.56    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(nnf_transformation,[],[f17])).
% 1.38/0.56  fof(f17,plain,(
% 1.38/0.56    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(flattening,[],[f16])).
% 1.38/0.56  fof(f16,plain,(
% 1.38/0.56    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f6])).
% 1.38/0.56  fof(f6,axiom,(
% 1.38/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 1.38/0.56  fof(f158,plain,(
% 1.38/0.56    ~spl7_7 | ~spl7_8 | spl7_1 | ~spl7_15 | spl7_16),
% 1.38/0.56    inference(avatar_split_clause,[],[f156,f149,f141,f65,f93,f90])).
% 1.38/0.56  fof(f141,plain,(
% 1.38/0.56    spl7_15 <=> r1_tarski(k1_relat_1(sK1),sK0)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.38/0.56  fof(f149,plain,(
% 1.38/0.56    spl7_16 <=> r2_hidden(sK4(sK1),sK0)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.38/0.56  fof(f156,plain,(
% 1.38/0.56    ~r1_tarski(k1_relat_1(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_16),
% 1.38/0.56    inference(resolution,[],[f155,f50])).
% 1.38/0.56  fof(f50,plain,(
% 1.38/0.56    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f33])).
% 1.38/0.56  fof(f155,plain,(
% 1.38/0.56    ( ! [X0] : (~r2_hidden(sK4(sK1),X0) | ~r1_tarski(X0,sK0)) ) | spl7_16),
% 1.38/0.56    inference(resolution,[],[f150,f55])).
% 1.38/0.56  fof(f55,plain,(
% 1.38/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f37])).
% 1.38/0.56  fof(f37,plain,(
% 1.38/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).
% 1.38/0.56  fof(f36,plain,(
% 1.38/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f35,plain,(
% 1.38/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.56    inference(rectify,[],[f34])).
% 1.38/0.56  fof(f34,plain,(
% 1.38/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.56    inference(nnf_transformation,[],[f18])).
% 1.38/0.56  fof(f18,plain,(
% 1.38/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f1])).
% 1.38/0.56  fof(f1,axiom,(
% 1.38/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.38/0.56  fof(f150,plain,(
% 1.38/0.56    ~r2_hidden(sK4(sK1),sK0) | spl7_16),
% 1.38/0.56    inference(avatar_component_clause,[],[f149])).
% 1.38/0.56  fof(f154,plain,(
% 1.38/0.56    ~spl7_16 | spl7_17 | ~spl7_12),
% 1.38/0.56    inference(avatar_split_clause,[],[f147,f124,f152,f149])).
% 1.38/0.56  fof(f124,plain,(
% 1.38/0.56    spl7_12 <=> ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.38/0.56  fof(f147,plain,(
% 1.38/0.56    sK4(sK1) = sK5(sK1) | ~r2_hidden(sK4(sK1),sK0) | ~spl7_12),
% 1.38/0.56    inference(equality_resolution,[],[f125])).
% 1.38/0.56  fof(f125,plain,(
% 1.38/0.56    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0)) ) | ~spl7_12),
% 1.38/0.56    inference(avatar_component_clause,[],[f124])).
% 1.38/0.56  fof(f145,plain,(
% 1.38/0.56    spl7_15),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f144])).
% 1.38/0.56  fof(f144,plain,(
% 1.38/0.56    $false | spl7_15),
% 1.38/0.56    inference(subsumption_resolution,[],[f129,f142])).
% 1.38/0.56  fof(f142,plain,(
% 1.38/0.56    ~r1_tarski(k1_relat_1(sK1),sK0) | spl7_15),
% 1.38/0.56    inference(avatar_component_clause,[],[f141])).
% 1.38/0.56  fof(f129,plain,(
% 1.38/0.56    r1_tarski(k1_relat_1(sK1),sK0)),
% 1.38/0.56    inference(resolution,[],[f115,f58])).
% 1.38/0.56  fof(f58,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f38])).
% 1.38/0.56  fof(f38,plain,(
% 1.38/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.38/0.56    inference(nnf_transformation,[],[f3])).
% 1.38/0.56  fof(f3,axiom,(
% 1.38/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.38/0.56  fof(f115,plain,(
% 1.38/0.56    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 1.38/0.56    inference(global_subsumption,[],[f41,f114])).
% 1.38/0.56  fof(f114,plain,(
% 1.38/0.56    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.38/0.56    inference(superposition,[],[f62,f100])).
% 1.38/0.56  fof(f100,plain,(
% 1.38/0.56    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 1.38/0.56    inference(resolution,[],[f41,f61])).
% 1.38/0.56  fof(f61,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f20])).
% 1.38/0.56  fof(f20,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.56    inference(ennf_transformation,[],[f9])).
% 1.38/0.56  fof(f9,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.38/0.56  fof(f62,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f21])).
% 1.38/0.56  fof(f21,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.56    inference(ennf_transformation,[],[f8])).
% 1.38/0.56  fof(f8,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.38/0.56  fof(f143,plain,(
% 1.38/0.56    ~spl7_7 | ~spl7_8 | spl7_1 | ~spl7_15 | spl7_11),
% 1.38/0.56    inference(avatar_split_clause,[],[f138,f121,f141,f65,f93,f90])).
% 1.38/0.56  fof(f121,plain,(
% 1.38/0.56    spl7_11 <=> r2_hidden(sK5(sK1),sK0)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.38/0.56  fof(f138,plain,(
% 1.38/0.56    ~r1_tarski(k1_relat_1(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_11),
% 1.38/0.56    inference(resolution,[],[f128,f51])).
% 1.38/0.56  fof(f51,plain,(
% 1.38/0.56    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f33])).
% 1.38/0.56  fof(f128,plain,(
% 1.38/0.56    ( ! [X0] : (~r2_hidden(sK5(sK1),X0) | ~r1_tarski(X0,sK0)) ) | spl7_11),
% 1.38/0.56    inference(resolution,[],[f122,f55])).
% 1.38/0.56  fof(f122,plain,(
% 1.38/0.56    ~r2_hidden(sK5(sK1),sK0) | spl7_11),
% 1.38/0.56    inference(avatar_component_clause,[],[f121])).
% 1.38/0.56  fof(f127,plain,(
% 1.38/0.56    ~spl7_11 | spl7_12 | ~spl7_6 | ~spl7_9),
% 1.38/0.56    inference(avatar_split_clause,[],[f117,f96,f85,f124,f121])).
% 1.38/0.56  fof(f85,plain,(
% 1.38/0.56    spl7_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.38/0.56  fof(f96,plain,(
% 1.38/0.56    spl7_9 <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.38/0.56  fof(f117,plain,(
% 1.38/0.56    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(sK5(sK1),sK0) | ~r2_hidden(X1,sK0) | sK5(sK1) = X1) ) | (~spl7_6 | ~spl7_9)),
% 1.38/0.56    inference(superposition,[],[f86,f97])).
% 1.38/0.56  fof(f97,plain,(
% 1.38/0.56    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~spl7_9),
% 1.38/0.56    inference(avatar_component_clause,[],[f96])).
% 1.38/0.56  fof(f86,plain,(
% 1.38/0.56    ( ! [X4,X5] : (k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | X4 = X5) ) | ~spl7_6),
% 1.38/0.56    inference(avatar_component_clause,[],[f85])).
% 1.38/0.56  fof(f113,plain,(
% 1.38/0.56    spl7_8),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f112])).
% 1.38/0.56  fof(f112,plain,(
% 1.38/0.56    $false | spl7_8),
% 1.38/0.56    inference(subsumption_resolution,[],[f39,f94])).
% 1.38/0.56  fof(f94,plain,(
% 1.38/0.56    ~v1_funct_1(sK1) | spl7_8),
% 1.38/0.56    inference(avatar_component_clause,[],[f93])).
% 1.38/0.56  fof(f111,plain,(
% 1.38/0.56    spl7_10),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f110])).
% 1.38/0.56  fof(f110,plain,(
% 1.38/0.56    $false | spl7_10),
% 1.38/0.56    inference(resolution,[],[f105,f54])).
% 1.38/0.56  fof(f54,plain,(
% 1.38/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f5])).
% 1.38/0.56  fof(f5,axiom,(
% 1.38/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.38/0.56  fof(f105,plain,(
% 1.38/0.56    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl7_10),
% 1.38/0.56    inference(avatar_component_clause,[],[f104])).
% 1.38/0.56  fof(f104,plain,(
% 1.38/0.56    spl7_10 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.38/0.56  fof(f107,plain,(
% 1.38/0.56    ~spl7_10 | spl7_7),
% 1.38/0.56    inference(avatar_split_clause,[],[f102,f90,f104])).
% 1.38/0.56  fof(f102,plain,(
% 1.38/0.56    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.38/0.56    inference(resolution,[],[f41,f48])).
% 1.38/0.56  fof(f48,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f15])).
% 1.38/0.56  fof(f15,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(ennf_transformation,[],[f4])).
% 1.38/0.56  fof(f4,axiom,(
% 1.38/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.38/0.56  fof(f98,plain,(
% 1.38/0.56    ~spl7_7 | ~spl7_8 | spl7_9 | spl7_1),
% 1.38/0.56    inference(avatar_split_clause,[],[f88,f65,f96,f93,f90])).
% 1.38/0.56  fof(f88,plain,(
% 1.38/0.56    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_1),
% 1.38/0.56    inference(resolution,[],[f66,f52])).
% 1.38/0.56  fof(f52,plain,(
% 1.38/0.56    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f33])).
% 1.38/0.56  fof(f66,plain,(
% 1.38/0.56    ~v2_funct_1(sK1) | spl7_1),
% 1.38/0.56    inference(avatar_component_clause,[],[f65])).
% 1.38/0.56  fof(f87,plain,(
% 1.38/0.56    spl7_1 | spl7_6),
% 1.38/0.56    inference(avatar_split_clause,[],[f42,f85,f65])).
% 1.38/0.56  fof(f42,plain,(
% 1.38/0.56    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0) | v2_funct_1(sK1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f29])).
% 1.38/0.56  fof(f82,plain,(
% 1.38/0.56    ~spl7_1 | spl7_5),
% 1.38/0.56    inference(avatar_split_clause,[],[f43,f80,f65])).
% 1.38/0.56  fof(f43,plain,(
% 1.38/0.56    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f29])).
% 1.38/0.56  fof(f78,plain,(
% 1.38/0.56    ~spl7_1 | spl7_4),
% 1.38/0.56    inference(avatar_split_clause,[],[f44,f76,f65])).
% 1.38/0.56  fof(f44,plain,(
% 1.38/0.56    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f29])).
% 1.38/0.56  fof(f74,plain,(
% 1.38/0.56    ~spl7_1 | spl7_3),
% 1.38/0.56    inference(avatar_split_clause,[],[f45,f72,f65])).
% 1.38/0.56  fof(f45,plain,(
% 1.38/0.56    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f29])).
% 1.38/0.56  fof(f70,plain,(
% 1.38/0.56    ~spl7_1 | ~spl7_2),
% 1.38/0.56    inference(avatar_split_clause,[],[f46,f68,f65])).
% 1.38/0.56  fof(f46,plain,(
% 1.38/0.56    sK2 != sK3 | ~v2_funct_1(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f29])).
% 1.38/0.56  % SZS output end Proof for theBenchmark
% 1.38/0.56  % (13557)------------------------------
% 1.38/0.56  % (13557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (13557)Termination reason: Refutation
% 1.38/0.56  
% 1.38/0.56  % (13557)Memory used [KB]: 10874
% 1.38/0.56  % (13557)Time elapsed: 0.126 s
% 1.38/0.56  % (13557)------------------------------
% 1.38/0.56  % (13557)------------------------------
% 1.38/0.56  % (13551)Success in time 0.196 s
%------------------------------------------------------------------------------
