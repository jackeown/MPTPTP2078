%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:48 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 329 expanded)
%              Number of leaves         :   34 ( 145 expanded)
%              Depth                    :   10
%              Number of atoms          :  480 (2384 expanded)
%              Number of equality atoms :   68 ( 517 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f72,f93,f95,f97,f112,f114,f118,f134,f149,f151,f169,f189,f191,f193,f213,f230,f252,f255])).

fof(f255,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl7_3 ),
    inference(resolution,[],[f77,f37])).

fof(f37,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f77,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl7_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f252,plain,(
    ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl7_22 ),
    inference(trivial_inequality_removal,[],[f250])).

fof(f250,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_22 ),
    inference(superposition,[],[f45,f232])).

fof(f232,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_22 ),
    inference(resolution,[],[f188,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f188,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl7_22
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f230,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl7_7 ),
    inference(trivial_inequality_removal,[],[f228])).

fof(f228,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_7 ),
    inference(superposition,[],[f45,f92])).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f213,plain,(
    ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl7_18 ),
    inference(resolution,[],[f194,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f194,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_18 ),
    inference(backward_demodulation,[],[f37,f168])).

fof(f168,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl7_18
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f193,plain,(
    spl7_16 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl7_16 ),
    inference(resolution,[],[f160,f39])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f160,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl7_16
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f191,plain,(
    spl7_21 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl7_21 ),
    inference(resolution,[],[f184,f43])).

fof(f43,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f184,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl7_21
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f189,plain,
    ( ~ spl7_21
    | spl7_22
    | spl7_17 ),
    inference(avatar_split_clause,[],[f180,f162,f186,f182])).

fof(f162,plain,
    ( spl7_17
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f180,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | spl7_17 ),
    inference(resolution,[],[f164,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f164,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f162])).

fof(f169,plain,
    ( ~ spl7_4
    | ~ spl7_16
    | ~ spl7_5
    | ~ spl7_17
    | spl7_18
    | ~ spl7_2
    | spl7_13 ),
    inference(avatar_split_clause,[],[f154,f131,f67,f166,f162,f83,f158,f79])).

fof(f79,plain,
    ( spl7_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f83,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f67,plain,
    ( spl7_2
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f131,plain,
    ( spl7_13
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f154,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_hidden(sK5,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ spl7_2
    | spl7_13 ),
    inference(resolution,[],[f152,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f152,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k2_relset_1(sK1,sK2,sK3))
    | ~ spl7_2
    | spl7_13 ),
    inference(resolution,[],[f137,f69])).

fof(f69,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK4))
        | ~ r2_hidden(k1_funct_1(sK3,sK5),X0) )
    | spl7_13 ),
    inference(resolution,[],[f133,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f133,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f151,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl7_12 ),
    inference(resolution,[],[f136,f42])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f136,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl7_12 ),
    inference(resolution,[],[f129,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f129,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_12
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f149,plain,(
    spl7_11 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl7_11 ),
    inference(resolution,[],[f135,f42])).

fof(f135,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_11 ),
    inference(resolution,[],[f125,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f125,plain,
    ( ~ v1_relat_1(sK4)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_11
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f134,plain,
    ( ~ spl7_11
    | ~ spl7_12
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f121,f105,f131,f109,f127,f123])).

fof(f109,plain,
    ( spl7_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f105,plain,
    ( spl7_9
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f121,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | ~ spl7_9 ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | ~ spl7_9 ),
    inference(superposition,[],[f119,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f119,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f46,f107])).

fof(f107,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f46,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f118,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl7_8 ),
    inference(resolution,[],[f103,f44])).

fof(f44,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f103,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl7_8
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f114,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl7_10 ),
    inference(resolution,[],[f111,f41])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f111,plain,
    ( ~ v1_funct_1(sK4)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f112,plain,
    ( ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f99,f87,f109,f105,f101])).

fof(f87,plain,
    ( spl7_6
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ m1_subset_1(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f99,plain,
    ( ~ v1_funct_1(sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl7_6 ),
    inference(resolution,[],[f98,f42])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f88,f43])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f97,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl7_5 ),
    inference(resolution,[],[f85,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f95,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl7_4 ),
    inference(resolution,[],[f81,f38])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,
    ( ~ v1_funct_1(sK3)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f93,plain,
    ( spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f73,f90,f87,f83,f79,f75])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
      | ~ m1_subset_1(X2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f54,f39])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f72,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f65,f42])).

fof(f65,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_1
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f70,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f61,f67,f63])).

fof(f61,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f44,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n015.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:33:38 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.45  % (15542)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.45  % (15542)Refutation found. Thanks to Tanya!
% 0.18/0.45  % SZS status Theorem for theBenchmark
% 0.18/0.47  % (15533)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f256,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(avatar_sat_refutation,[],[f70,f72,f93,f95,f97,f112,f114,f118,f134,f149,f151,f169,f189,f191,f193,f213,f230,f252,f255])).
% 0.18/0.47  fof(f255,plain,(
% 0.18/0.47    ~spl7_3),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f253])).
% 0.18/0.47  fof(f253,plain,(
% 0.18/0.47    $false | ~spl7_3),
% 0.18/0.47    inference(resolution,[],[f77,f37])).
% 0.18/0.47  fof(f37,plain,(
% 0.18/0.47    ~v1_xboole_0(sK2)),
% 0.18/0.47    inference(cnf_transformation,[],[f32])).
% 0.18/0.47  fof(f32,plain,(
% 0.18/0.47    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f31,f30,f29,f28])).
% 0.18/0.47  fof(f28,plain,(
% 0.18/0.47    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f29,plain,(
% 0.18/0.47    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f30,plain,(
% 0.18/0.47    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f31,plain,(
% 0.18/0.47    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f14,plain,(
% 0.18/0.47    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.18/0.47    inference(flattening,[],[f13])).
% 0.18/0.47  fof(f13,plain,(
% 0.18/0.47    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.18/0.47    inference(ennf_transformation,[],[f12])).
% 0.18/0.47  fof(f12,negated_conjecture,(
% 0.18/0.47    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.18/0.47    inference(negated_conjecture,[],[f11])).
% 0.18/0.47  fof(f11,conjecture,(
% 0.18/0.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.18/0.47  fof(f77,plain,(
% 0.18/0.47    v1_xboole_0(sK2) | ~spl7_3),
% 0.18/0.47    inference(avatar_component_clause,[],[f75])).
% 0.18/0.47  fof(f75,plain,(
% 0.18/0.47    spl7_3 <=> v1_xboole_0(sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.18/0.47  fof(f252,plain,(
% 0.18/0.47    ~spl7_22),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f251])).
% 0.18/0.47  fof(f251,plain,(
% 0.18/0.47    $false | ~spl7_22),
% 0.18/0.47    inference(trivial_inequality_removal,[],[f250])).
% 0.18/0.47  fof(f250,plain,(
% 0.18/0.47    k1_xboole_0 != k1_xboole_0 | ~spl7_22),
% 0.18/0.47    inference(superposition,[],[f45,f232])).
% 0.18/0.47  fof(f232,plain,(
% 0.18/0.47    k1_xboole_0 = sK1 | ~spl7_22),
% 0.18/0.47    inference(resolution,[],[f188,f48])).
% 0.18/0.47  fof(f48,plain,(
% 0.18/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.18/0.47    inference(cnf_transformation,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f3])).
% 0.18/0.47  fof(f3,axiom,(
% 0.18/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.18/0.47  fof(f188,plain,(
% 0.18/0.47    v1_xboole_0(sK1) | ~spl7_22),
% 0.18/0.47    inference(avatar_component_clause,[],[f186])).
% 0.18/0.47  fof(f186,plain,(
% 0.18/0.47    spl7_22 <=> v1_xboole_0(sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.18/0.47  fof(f45,plain,(
% 0.18/0.47    k1_xboole_0 != sK1),
% 0.18/0.47    inference(cnf_transformation,[],[f32])).
% 0.18/0.47  fof(f230,plain,(
% 0.18/0.47    ~spl7_7),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f229])).
% 0.18/0.47  fof(f229,plain,(
% 0.18/0.47    $false | ~spl7_7),
% 0.18/0.47    inference(trivial_inequality_removal,[],[f228])).
% 0.18/0.47  fof(f228,plain,(
% 0.18/0.47    k1_xboole_0 != k1_xboole_0 | ~spl7_7),
% 0.18/0.47    inference(superposition,[],[f45,f92])).
% 0.18/0.47  fof(f92,plain,(
% 0.18/0.47    k1_xboole_0 = sK1 | ~spl7_7),
% 0.18/0.47    inference(avatar_component_clause,[],[f90])).
% 0.18/0.47  fof(f90,plain,(
% 0.18/0.47    spl7_7 <=> k1_xboole_0 = sK1),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.18/0.47  fof(f213,plain,(
% 0.18/0.47    ~spl7_18),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f212])).
% 0.18/0.47  fof(f212,plain,(
% 0.18/0.47    $false | ~spl7_18),
% 0.18/0.47    inference(resolution,[],[f194,f47])).
% 0.18/0.47  fof(f47,plain,(
% 0.18/0.47    v1_xboole_0(k1_xboole_0)),
% 0.18/0.47    inference(cnf_transformation,[],[f2])).
% 0.18/0.47  fof(f2,axiom,(
% 0.18/0.47    v1_xboole_0(k1_xboole_0)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.18/0.47  fof(f194,plain,(
% 0.18/0.47    ~v1_xboole_0(k1_xboole_0) | ~spl7_18),
% 0.18/0.47    inference(backward_demodulation,[],[f37,f168])).
% 0.18/0.47  fof(f168,plain,(
% 0.18/0.47    k1_xboole_0 = sK2 | ~spl7_18),
% 0.18/0.47    inference(avatar_component_clause,[],[f166])).
% 0.18/0.47  fof(f166,plain,(
% 0.18/0.47    spl7_18 <=> k1_xboole_0 = sK2),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.18/0.47  fof(f193,plain,(
% 0.18/0.47    spl7_16),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f192])).
% 0.18/0.47  fof(f192,plain,(
% 0.18/0.47    $false | spl7_16),
% 0.18/0.47    inference(resolution,[],[f160,f39])).
% 0.18/0.47  fof(f39,plain,(
% 0.18/0.47    v1_funct_2(sK3,sK1,sK2)),
% 0.18/0.47    inference(cnf_transformation,[],[f32])).
% 0.18/0.47  fof(f160,plain,(
% 0.18/0.47    ~v1_funct_2(sK3,sK1,sK2) | spl7_16),
% 0.18/0.47    inference(avatar_component_clause,[],[f158])).
% 0.18/0.47  fof(f158,plain,(
% 0.18/0.47    spl7_16 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.18/0.47  fof(f191,plain,(
% 0.18/0.47    spl7_21),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f190])).
% 0.18/0.47  fof(f190,plain,(
% 0.18/0.47    $false | spl7_21),
% 0.18/0.47    inference(resolution,[],[f184,f43])).
% 0.18/0.47  fof(f43,plain,(
% 0.18/0.47    m1_subset_1(sK5,sK1)),
% 0.18/0.47    inference(cnf_transformation,[],[f32])).
% 0.18/0.47  fof(f184,plain,(
% 0.18/0.47    ~m1_subset_1(sK5,sK1) | spl7_21),
% 0.18/0.47    inference(avatar_component_clause,[],[f182])).
% 0.18/0.47  fof(f182,plain,(
% 0.18/0.47    spl7_21 <=> m1_subset_1(sK5,sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.18/0.47  fof(f189,plain,(
% 0.18/0.47    ~spl7_21 | spl7_22 | spl7_17),
% 0.18/0.47    inference(avatar_split_clause,[],[f180,f162,f186,f182])).
% 0.18/0.47  fof(f162,plain,(
% 0.18/0.47    spl7_17 <=> r2_hidden(sK5,sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.18/0.47  fof(f180,plain,(
% 0.18/0.47    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | spl7_17),
% 0.18/0.47    inference(resolution,[],[f164,f49])).
% 0.18/0.47  fof(f49,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f17])).
% 0.18/0.47  fof(f17,plain,(
% 0.18/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.18/0.47    inference(flattening,[],[f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f4])).
% 0.18/0.47  fof(f4,axiom,(
% 0.18/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.18/0.47  fof(f164,plain,(
% 0.18/0.47    ~r2_hidden(sK5,sK1) | spl7_17),
% 0.18/0.47    inference(avatar_component_clause,[],[f162])).
% 0.18/0.47  fof(f169,plain,(
% 0.18/0.47    ~spl7_4 | ~spl7_16 | ~spl7_5 | ~spl7_17 | spl7_18 | ~spl7_2 | spl7_13),
% 0.18/0.47    inference(avatar_split_clause,[],[f154,f131,f67,f166,f162,f83,f158,f79])).
% 0.18/0.47  fof(f79,plain,(
% 0.18/0.47    spl7_4 <=> v1_funct_1(sK3)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.18/0.47  fof(f83,plain,(
% 0.18/0.47    spl7_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.18/0.47  fof(f67,plain,(
% 0.18/0.47    spl7_2 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.18/0.47  fof(f131,plain,(
% 0.18/0.47    spl7_13 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.18/0.47  fof(f154,plain,(
% 0.18/0.47    k1_xboole_0 = sK2 | ~r2_hidden(sK5,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | (~spl7_2 | spl7_13)),
% 0.18/0.47    inference(resolution,[],[f152,f59])).
% 0.18/0.47  fof(f59,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f27])).
% 0.18/0.47  fof(f27,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.18/0.47    inference(flattening,[],[f26])).
% 0.18/0.47  fof(f26,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.18/0.47    inference(ennf_transformation,[],[f10])).
% 0.18/0.47  fof(f10,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.18/0.47  fof(f152,plain,(
% 0.18/0.47    ~r2_hidden(k1_funct_1(sK3,sK5),k2_relset_1(sK1,sK2,sK3)) | (~spl7_2 | spl7_13)),
% 0.18/0.47    inference(resolution,[],[f137,f69])).
% 0.18/0.47  fof(f69,plain,(
% 0.18/0.47    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~spl7_2),
% 0.18/0.47    inference(avatar_component_clause,[],[f67])).
% 0.18/0.47  fof(f137,plain,(
% 0.18/0.47    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK4)) | ~r2_hidden(k1_funct_1(sK3,sK5),X0)) ) | spl7_13),
% 0.18/0.47    inference(resolution,[],[f133,f51])).
% 0.18/0.47  fof(f51,plain,(
% 0.18/0.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f36])).
% 0.18/0.47  fof(f36,plain,(
% 0.18/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 0.18/0.47  fof(f35,plain,(
% 0.18/0.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f34,plain,(
% 0.18/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.47    inference(rectify,[],[f33])).
% 0.18/0.47  fof(f33,plain,(
% 0.18/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.47    inference(nnf_transformation,[],[f20])).
% 0.18/0.47  fof(f20,plain,(
% 0.18/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.18/0.47    inference(ennf_transformation,[],[f1])).
% 0.18/0.47  fof(f1,axiom,(
% 0.18/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.18/0.47  fof(f133,plain,(
% 0.18/0.47    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl7_13),
% 0.18/0.47    inference(avatar_component_clause,[],[f131])).
% 0.18/0.47  fof(f151,plain,(
% 0.18/0.47    spl7_12),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f150])).
% 0.18/0.47  fof(f150,plain,(
% 0.18/0.47    $false | spl7_12),
% 0.18/0.47    inference(resolution,[],[f136,f42])).
% 0.18/0.47  fof(f42,plain,(
% 0.18/0.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.18/0.47    inference(cnf_transformation,[],[f32])).
% 0.18/0.47  fof(f136,plain,(
% 0.18/0.47    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl7_12),
% 0.18/0.47    inference(resolution,[],[f129,f58])).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f25])).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f6])).
% 0.18/0.47  fof(f6,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.47  fof(f129,plain,(
% 0.18/0.47    ~v5_relat_1(sK4,sK0) | spl7_12),
% 0.18/0.47    inference(avatar_component_clause,[],[f127])).
% 0.18/0.47  fof(f127,plain,(
% 0.18/0.47    spl7_12 <=> v5_relat_1(sK4,sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.18/0.47  fof(f149,plain,(
% 0.18/0.47    spl7_11),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f148])).
% 0.18/0.47  fof(f148,plain,(
% 0.18/0.47    $false | spl7_11),
% 0.18/0.47    inference(resolution,[],[f135,f42])).
% 0.18/0.47  fof(f135,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_11),
% 0.18/0.47    inference(resolution,[],[f125,f55])).
% 0.18/0.47  fof(f55,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f23])).
% 0.18/0.47  fof(f23,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f5])).
% 0.18/0.47  fof(f5,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.47  fof(f125,plain,(
% 0.18/0.47    ~v1_relat_1(sK4) | spl7_11),
% 0.18/0.47    inference(avatar_component_clause,[],[f123])).
% 0.18/0.47  fof(f123,plain,(
% 0.18/0.47    spl7_11 <=> v1_relat_1(sK4)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.18/0.47  fof(f134,plain,(
% 0.18/0.47    ~spl7_11 | ~spl7_12 | ~spl7_10 | ~spl7_13 | ~spl7_9),
% 0.18/0.47    inference(avatar_split_clause,[],[f121,f105,f131,f109,f127,f123])).
% 0.18/0.47  fof(f109,plain,(
% 0.18/0.47    spl7_10 <=> v1_funct_1(sK4)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.18/0.47  fof(f105,plain,(
% 0.18/0.47    spl7_9 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.18/0.47  fof(f121,plain,(
% 0.18/0.47    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | ~spl7_9),
% 0.18/0.47    inference(trivial_inequality_removal,[],[f120])).
% 0.18/0.47  fof(f120,plain,(
% 0.18/0.47    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | ~spl7_9),
% 0.18/0.47    inference(superposition,[],[f119,f50])).
% 0.18/0.47  fof(f50,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f19])).
% 0.18/0.47  fof(f19,plain,(
% 0.18/0.47    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(flattening,[],[f18])).
% 0.18/0.47  fof(f18,plain,(
% 0.18/0.47    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.18/0.47    inference(ennf_transformation,[],[f8])).
% 0.18/0.47  fof(f8,axiom,(
% 0.18/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.18/0.47  fof(f119,plain,(
% 0.18/0.47    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl7_9),
% 0.18/0.47    inference(backward_demodulation,[],[f46,f107])).
% 0.18/0.47  fof(f107,plain,(
% 0.18/0.47    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl7_9),
% 0.18/0.47    inference(avatar_component_clause,[],[f105])).
% 0.18/0.47  fof(f46,plain,(
% 0.18/0.47    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.18/0.47    inference(cnf_transformation,[],[f32])).
% 0.18/0.47  fof(f118,plain,(
% 0.18/0.47    spl7_8),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f115])).
% 0.18/0.47  fof(f115,plain,(
% 0.18/0.47    $false | spl7_8),
% 0.18/0.47    inference(resolution,[],[f103,f44])).
% 0.18/0.47  fof(f44,plain,(
% 0.18/0.47    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.18/0.47    inference(cnf_transformation,[],[f32])).
% 0.18/0.47  fof(f103,plain,(
% 0.18/0.47    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | spl7_8),
% 0.18/0.47    inference(avatar_component_clause,[],[f101])).
% 0.18/0.47  fof(f101,plain,(
% 0.18/0.47    spl7_8 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.18/0.47  fof(f114,plain,(
% 0.18/0.47    spl7_10),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f113])).
% 0.18/0.47  fof(f113,plain,(
% 0.18/0.47    $false | spl7_10),
% 0.18/0.47    inference(resolution,[],[f111,f41])).
% 0.18/0.47  fof(f41,plain,(
% 0.18/0.47    v1_funct_1(sK4)),
% 0.18/0.47    inference(cnf_transformation,[],[f32])).
% 0.18/0.47  fof(f111,plain,(
% 0.18/0.47    ~v1_funct_1(sK4) | spl7_10),
% 0.18/0.47    inference(avatar_component_clause,[],[f109])).
% 0.18/0.47  fof(f112,plain,(
% 0.18/0.47    ~spl7_8 | spl7_9 | ~spl7_10 | ~spl7_6),
% 0.18/0.47    inference(avatar_split_clause,[],[f99,f87,f109,f105,f101])).
% 0.18/0.47  fof(f87,plain,(
% 0.18/0.47    spl7_6 <=> ! [X1,X0,X2] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(X2,sK1))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.18/0.47  fof(f99,plain,(
% 0.18/0.47    ~v1_funct_1(sK4) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl7_6),
% 0.18/0.47    inference(resolution,[],[f98,f42])).
% 0.18/0.47  fof(f98,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))) ) | ~spl7_6),
% 0.18/0.47    inference(resolution,[],[f88,f43])).
% 0.18/0.47  fof(f88,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,sK1) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))) ) | ~spl7_6),
% 0.18/0.47    inference(avatar_component_clause,[],[f87])).
% 0.18/0.47  fof(f97,plain,(
% 0.18/0.47    spl7_5),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f96])).
% 0.18/0.47  fof(f96,plain,(
% 0.18/0.47    $false | spl7_5),
% 0.18/0.47    inference(resolution,[],[f85,f40])).
% 0.18/0.47  fof(f40,plain,(
% 0.18/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.18/0.47    inference(cnf_transformation,[],[f32])).
% 0.18/0.47  fof(f85,plain,(
% 0.18/0.47    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl7_5),
% 0.18/0.47    inference(avatar_component_clause,[],[f83])).
% 0.18/0.47  fof(f95,plain,(
% 0.18/0.47    spl7_4),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f94])).
% 0.18/0.47  fof(f94,plain,(
% 0.18/0.47    $false | spl7_4),
% 0.18/0.47    inference(resolution,[],[f81,f38])).
% 0.18/0.47  fof(f38,plain,(
% 0.18/0.47    v1_funct_1(sK3)),
% 0.18/0.47    inference(cnf_transformation,[],[f32])).
% 0.18/0.47  fof(f81,plain,(
% 0.18/0.47    ~v1_funct_1(sK3) | spl7_4),
% 0.18/0.47    inference(avatar_component_clause,[],[f79])).
% 0.18/0.47  fof(f93,plain,(
% 0.18/0.47    spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | spl7_7),
% 0.18/0.47    inference(avatar_split_clause,[],[f73,f90,f87,f83,f79,f75])).
% 0.18/0.47  fof(f73,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(X2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) )),
% 0.18/0.47    inference(resolution,[],[f54,f39])).
% 0.18/0.47  fof(f54,plain,(
% 0.18/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X3,X1,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f22])).
% 0.18/0.47  fof(f22,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.18/0.47    inference(flattening,[],[f21])).
% 0.18/0.47  fof(f21,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.18/0.47    inference(ennf_transformation,[],[f9])).
% 0.18/0.47  fof(f9,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.18/0.47  fof(f72,plain,(
% 0.18/0.47    spl7_1),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f71])).
% 0.18/0.47  fof(f71,plain,(
% 0.18/0.47    $false | spl7_1),
% 0.18/0.47    inference(resolution,[],[f65,f42])).
% 0.18/0.47  fof(f65,plain,(
% 0.18/0.47    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | spl7_1),
% 0.18/0.47    inference(avatar_component_clause,[],[f63])).
% 0.18/0.47  fof(f63,plain,(
% 0.18/0.47    spl7_1 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.18/0.47  fof(f70,plain,(
% 0.18/0.47    ~spl7_1 | spl7_2),
% 0.18/0.47    inference(avatar_split_clause,[],[f61,f67,f63])).
% 0.18/0.47  fof(f61,plain,(
% 0.18/0.47    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.18/0.47    inference(superposition,[],[f44,f56])).
% 0.18/0.47  fof(f56,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f24])).
% 0.18/0.47  fof(f24,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f7])).
% 0.18/0.47  fof(f7,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.18/0.47  % SZS output end Proof for theBenchmark
% 0.18/0.47  % (15542)------------------------------
% 0.18/0.47  % (15542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (15542)Termination reason: Refutation
% 0.18/0.47  
% 0.18/0.47  % (15542)Memory used [KB]: 6268
% 0.18/0.47  % (15542)Time elapsed: 0.087 s
% 0.18/0.47  % (15542)------------------------------
% 0.18/0.47  % (15542)------------------------------
% 0.18/0.48  % (15525)Success in time 0.138 s
%------------------------------------------------------------------------------
