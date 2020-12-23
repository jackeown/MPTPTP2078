%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:41 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  247 ( 928 expanded)
%              Number of leaves         :   38 ( 285 expanded)
%              Depth                    :   24
%              Number of atoms          :  868 (5451 expanded)
%              Number of equality atoms :  187 ( 417 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f879,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f165,f220,f229,f233,f273,f401,f431,f487,f878])).

fof(f878,plain,
    ( ~ spl4_2
    | ~ spl4_5
    | ~ spl4_7
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f877])).

fof(f877,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_7
    | spl4_8 ),
    inference(subsumption_resolution,[],[f876,f416])).

fof(f416,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl4_8
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f876,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f874,f326])).

fof(f326,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f262,f309])).

fof(f309,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(resolution,[],[f283,f86])).

fof(f86,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f283,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK1 = X0 )
    | ~ spl4_2 ),
    inference(resolution,[],[f164,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f164,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f262,plain,
    ( sK1 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f223,f219])).

fof(f219,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f223,plain,(
    sK1 = k7_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f222,f145])).

fof(f145,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f79,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f65,f64])).

fof(f64,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

fof(f222,plain,
    ( sK1 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f147,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f147,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f79,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f874,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f872,f400])).

fof(f400,plain,
    ( k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl4_7
  <=> k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f872,plain,
    ( ! [X4] : k1_partfun1(X4,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k7_relat_1(k1_xboole_0,k1_partfun1(X4,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f833,f313])).

fof(f313,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f145,f309])).

fof(f833,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k1_partfun1(X1,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k7_relat_1(X0,k1_partfun1(X1,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f832,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f832,plain,
    ( ! [X2,X1] : r1_tarski(k1_partfun1(X1,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X2)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f828,f88])).

fof(f88,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f828,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k1_partfun1(X1,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X2)
        | ~ r1_tarski(k1_xboole_0,sK3(k1_partfun1(X1,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X2)) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f657,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f657,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k1_partfun1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1),k1_xboole_0)
        | r1_tarski(k1_partfun1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f576,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f69,f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
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

fof(f576,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k1_partfun1(X6,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
        | r2_hidden(X5,k1_xboole_0) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f513,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f513,plain,
    ( ! [X2] : m1_subset_1(k1_partfun1(X2,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f511,f312])).

fof(f312,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f76,f309])).

fof(f76,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f511,plain,
    ( ! [X2] :
        ( m1_subset_1(k1_partfun1(X2,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f448,f329])).

fof(f329,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f265,f309])).

fof(f265,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f236,f140])).

fof(f140,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f236,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f79,f219])).

fof(f448,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | m1_subset_1(k1_partfun1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X1) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f334,f140])).

fof(f334,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | m1_subset_1(k1_partfun1(X1,X2,k1_xboole_0,k1_xboole_0,X3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X3) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f274,f309])).

fof(f274,plain,
    ( ! [X2,X3,X1] :
        ( m1_subset_1(k1_partfun1(X1,X2,k1_xboole_0,k1_xboole_0,X3,sK1),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3) )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f249,f140])).

fof(f249,plain,
    ( ! [X2,X3,X1] :
        ( m1_subset_1(k1_partfun1(X1,X2,k1_xboole_0,k1_xboole_0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3) )
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f170,f219])).

fof(f170,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(k1_partfun1(X1,X2,sK0,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f152,f76])).

fof(f152,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(k1_partfun1(X1,X2,sK0,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f79,f129])).

fof(f129,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f487,plain,
    ( ~ spl4_2
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f484,f396])).

fof(f396,plain,
    ( ~ m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl4_6
  <=> m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f484,plain,
    ( m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f450,f130])).

fof(f130,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f87,f89])).

fof(f89,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f87,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f450,plain,
    ( ! [X3] : m1_subset_1(k1_partfun1(X3,X3,k1_xboole_0,k1_xboole_0,k6_partfun1(X3),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f447,f133])).

fof(f133,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f93,f89])).

fof(f93,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f447,plain,
    ( ! [X3] :
        ( m1_subset_1(k1_partfun1(X3,X3,k1_xboole_0,k1_xboole_0,k6_partfun1(X3),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(k6_partfun1(X3)) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f334,f94])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f431,plain,
    ( ~ spl4_2
    | spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | ~ spl4_2
    | spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f429,f363])).

fof(f363,plain,
    ( k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | ~ spl4_2
    | spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f317,f340])).

fof(f340,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f311,f309])).

fof(f311,plain,
    ( sK1 = sK2
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f283,f281])).

fof(f281,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f280,f86])).

fof(f280,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f175,f219])).

fof(f175,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f83,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f66])).

fof(f317,plain,
    ( sK2 != k2_funct_1(k1_xboole_0)
    | ~ spl4_2
    | spl4_4 ),
    inference(backward_demodulation,[],[f214,f309])).

fof(f214,plain,
    ( sK2 != k2_funct_1(sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl4_4
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f429,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f423,f130])).

fof(f423,plain,
    ( k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f389,f417])).

fof(f417,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f415])).

fof(f389,plain,
    ( k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f388,f130])).

fof(f388,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f387,f327])).

fof(f327,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f263,f309])).

fof(f263,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f226,f219])).

fof(f226,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f225,f145])).

fof(f225,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f224,f148])).

fof(f148,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f79,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f224,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f169,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f169,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f168,f76])).

fof(f168,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f150,f78])).

fof(f78,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f150,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(resolution,[],[f79,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f387,plain,
    ( k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0))
    | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f386,f313])).

fof(f386,plain,
    ( k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0))
    | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f385,f312])).

fof(f385,plain,
    ( k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0))
    | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f384,f134])).

fof(f134,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f92,f89])).

fof(f92,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f384,plain,
    ( k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0))
    | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f383,f133])).

fof(f383,plain,
    ( k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0))
    | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_relat_1(k1_xboole_0)))
    | ~ v1_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f382,f315])).

fof(f315,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f167,f309])).

fof(f167,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f166,f76])).

fof(f166,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f149,f78])).

fof(f149,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f79,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f382,plain,
    ( k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0))
    | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_relat_1(k1_xboole_0)))
    | ~ v1_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f381,f135])).

fof(f135,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f96,f89])).

fof(f96,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f381,plain,
    ( k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0))
    | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k2_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0)))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_relat_1(k1_xboole_0)))
    | ~ v1_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(superposition,[],[f138,f316])).

fof(f316,plain,
    ( k1_xboole_0 = k5_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f196,f309])).

fof(f196,plain,(
    sK1 = k5_relat_1(k6_partfun1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f145,f137])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f97,f89])).

fof(f97,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f138,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f98,f89])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f401,plain,
    ( ~ spl4_6
    | spl4_7
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f392,f217,f162,f398,f394])).

fof(f392,plain,
    ( k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f337,f365])).

fof(f365,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f330,f340])).

fof(f330,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f267,f309])).

fof(f267,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK2),k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f240,f130])).

fof(f240,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK2),k6_partfun1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f84,f219])).

fof(f84,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

fof(f337,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f331,f309])).

fof(f331,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,X0,sK1) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f269,f309])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,X0,sK1)
        | sK1 = X0 )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f268,f140])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,X0,sK1)
        | sK1 = X0 )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f243,f219])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,X0,sK1)
        | sK1 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f151,f219])).

fof(f151,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK0,sK0,X0,sK1)
      | sK1 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    inference(resolution,[],[f79,f126])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f273,plain,
    ( spl4_1
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl4_1
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f247,f86])).

fof(f247,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_1
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f160,f219])).

fof(f160,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f233,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f230,f184])).

fof(f184,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f83,f143])).

fof(f143,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f230,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f174,f215])).

fof(f215,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f213])).

fof(f174,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f85,f173])).

fof(f173,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f172,f76])).

fof(f172,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f171,f77])).

fof(f77,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f171,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f154,f78])).

fof(f154,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f79,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f85,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f229,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f227,f211])).

fof(f211,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl4_3
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f227,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f146,f226])).

fof(f146,plain,(
    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(resolution,[],[f79,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f220,plain,
    ( ~ spl4_3
    | spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f207,f217,f213,f209])).

fof(f207,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f206,f76])).

fof(f206,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f205,f77])).

fof(f205,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f204,f79])).

fof(f204,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f203,f80])).

fof(f80,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f203,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f202,f81])).

fof(f81,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f202,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f201,f83])).

fof(f201,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f200,f167])).

fof(f200,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f84,f125])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = X3
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f165,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f144,f162,f158])).

fof(f144,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f79,f99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (9216)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (9223)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (9239)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (9219)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (9217)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (9228)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (9220)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (9231)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (9227)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (9241)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (9218)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (9230)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (9245)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (9238)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (9229)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (9236)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (9222)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (9234)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (9232)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (9221)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (9235)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (9242)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (9225)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (9246)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (9244)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (9233)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.55  % (9237)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.46/0.55  % (9226)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.55  % (9224)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.55  % (9243)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.59/0.58  % (9237)Refutation not found, incomplete strategy% (9237)------------------------------
% 1.59/0.58  % (9237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (9237)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (9237)Memory used [KB]: 1918
% 1.59/0.58  % (9237)Time elapsed: 0.181 s
% 1.59/0.58  % (9237)------------------------------
% 1.59/0.58  % (9237)------------------------------
% 1.59/0.58  % (9224)Refutation found. Thanks to Tanya!
% 1.59/0.58  % SZS status Theorem for theBenchmark
% 1.59/0.58  % SZS output start Proof for theBenchmark
% 1.59/0.58  fof(f879,plain,(
% 1.59/0.58    $false),
% 1.59/0.58    inference(avatar_sat_refutation,[],[f165,f220,f229,f233,f273,f401,f431,f487,f878])).
% 1.59/0.58  fof(f878,plain,(
% 1.59/0.58    ~spl4_2 | ~spl4_5 | ~spl4_7 | spl4_8),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f877])).
% 1.59/0.58  fof(f877,plain,(
% 1.59/0.58    $false | (~spl4_2 | ~spl4_5 | ~spl4_7 | spl4_8)),
% 1.59/0.58    inference(subsumption_resolution,[],[f876,f416])).
% 1.59/0.58  fof(f416,plain,(
% 1.59/0.58    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl4_8),
% 1.59/0.58    inference(avatar_component_clause,[],[f415])).
% 1.59/0.58  fof(f415,plain,(
% 1.59/0.58    spl4_8 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.59/0.58  fof(f876,plain,(
% 1.59/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_2 | ~spl4_5 | ~spl4_7)),
% 1.59/0.58    inference(forward_demodulation,[],[f874,f326])).
% 1.59/0.58  fof(f326,plain,(
% 1.59/0.58    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl4_2 | ~spl4_5)),
% 1.59/0.58    inference(backward_demodulation,[],[f262,f309])).
% 1.59/0.58  fof(f309,plain,(
% 1.59/0.58    k1_xboole_0 = sK1 | ~spl4_2),
% 1.59/0.58    inference(resolution,[],[f283,f86])).
% 1.59/0.58  fof(f86,plain,(
% 1.59/0.58    v1_xboole_0(k1_xboole_0)),
% 1.59/0.58    inference(cnf_transformation,[],[f2])).
% 1.59/0.58  fof(f2,axiom,(
% 1.59/0.58    v1_xboole_0(k1_xboole_0)),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.59/0.58  fof(f283,plain,(
% 1.59/0.58    ( ! [X0] : (~v1_xboole_0(X0) | sK1 = X0) ) | ~spl4_2),
% 1.59/0.58    inference(resolution,[],[f164,f114])).
% 1.59/0.58  fof(f114,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f49])).
% 1.59/0.58  fof(f49,plain,(
% 1.59/0.58    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f4])).
% 1.59/0.58  fof(f4,axiom,(
% 1.59/0.58    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.59/0.58  fof(f164,plain,(
% 1.59/0.58    v1_xboole_0(sK1) | ~spl4_2),
% 1.59/0.58    inference(avatar_component_clause,[],[f162])).
% 1.59/0.58  fof(f162,plain,(
% 1.59/0.58    spl4_2 <=> v1_xboole_0(sK1)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.59/0.58  fof(f262,plain,(
% 1.59/0.58    sK1 = k7_relat_1(sK1,k1_xboole_0) | ~spl4_5),
% 1.59/0.58    inference(backward_demodulation,[],[f223,f219])).
% 1.59/0.58  fof(f219,plain,(
% 1.59/0.58    k1_xboole_0 = sK0 | ~spl4_5),
% 1.59/0.58    inference(avatar_component_clause,[],[f217])).
% 1.59/0.58  fof(f217,plain,(
% 1.59/0.58    spl4_5 <=> k1_xboole_0 = sK0),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.59/0.58  fof(f223,plain,(
% 1.59/0.58    sK1 = k7_relat_1(sK1,sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f222,f145])).
% 1.59/0.58  fof(f145,plain,(
% 1.59/0.58    v1_relat_1(sK1)),
% 1.59/0.58    inference(resolution,[],[f79,f116])).
% 1.59/0.58  fof(f116,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f51])).
% 1.59/0.58  fof(f51,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.58    inference(ennf_transformation,[],[f17])).
% 1.59/0.58  fof(f17,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.59/0.58  fof(f79,plain,(
% 1.59/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.59/0.58    inference(cnf_transformation,[],[f66])).
% 1.59/0.58  fof(f66,plain,(
% 1.59/0.58    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f65,f64])).
% 1.59/0.58  fof(f64,plain,(
% 1.59/0.58    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f65,plain,(
% 1.59/0.58    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f34,plain,(
% 1.59/0.58    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.59/0.58    inference(flattening,[],[f33])).
% 1.59/0.58  fof(f33,plain,(
% 1.59/0.58    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.59/0.58    inference(ennf_transformation,[],[f31])).
% 1.59/0.58  fof(f31,negated_conjecture,(
% 1.59/0.58    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.59/0.58    inference(negated_conjecture,[],[f30])).
% 1.59/0.58  fof(f30,conjecture,(
% 1.59/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 1.59/0.58  fof(f222,plain,(
% 1.59/0.58    sK1 = k7_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.59/0.58    inference(resolution,[],[f147,f102])).
% 1.59/0.58  fof(f102,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f43])).
% 1.59/0.58  fof(f43,plain,(
% 1.59/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(flattening,[],[f42])).
% 1.59/0.58  fof(f42,plain,(
% 1.59/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.59/0.58    inference(ennf_transformation,[],[f8])).
% 1.59/0.58  fof(f8,axiom,(
% 1.59/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.59/0.58  fof(f147,plain,(
% 1.59/0.58    v4_relat_1(sK1,sK0)),
% 1.59/0.58    inference(resolution,[],[f79,f118])).
% 1.59/0.58  fof(f118,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f53])).
% 1.59/0.58  fof(f53,plain,(
% 1.59/0.58    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.58    inference(ennf_transformation,[],[f18])).
% 1.59/0.58  fof(f18,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.59/0.58  fof(f874,plain,(
% 1.59/0.58    k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) | (~spl4_2 | ~spl4_5 | ~spl4_7)),
% 1.59/0.58    inference(superposition,[],[f872,f400])).
% 1.59/0.58  fof(f400,plain,(
% 1.59/0.58    k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl4_7),
% 1.59/0.58    inference(avatar_component_clause,[],[f398])).
% 1.59/0.58  fof(f398,plain,(
% 1.59/0.58    spl4_7 <=> k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.59/0.58  fof(f872,plain,(
% 1.59/0.58    ( ! [X4] : (k1_partfun1(X4,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k7_relat_1(k1_xboole_0,k1_partfun1(X4,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.58    inference(resolution,[],[f833,f313])).
% 1.59/0.58  fof(f313,plain,(
% 1.59/0.58    v1_relat_1(k1_xboole_0) | ~spl4_2),
% 1.59/0.58    inference(backward_demodulation,[],[f145,f309])).
% 1.59/0.58  fof(f833,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_partfun1(X1,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k7_relat_1(X0,k1_partfun1(X1,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.58    inference(resolution,[],[f832,f100])).
% 1.59/0.58  fof(f100,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f40])).
% 1.59/0.58  fof(f40,plain,(
% 1.59/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(flattening,[],[f39])).
% 1.59/0.58  fof(f39,plain,(
% 1.59/0.58    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f12])).
% 1.59/0.58  fof(f12,axiom,(
% 1.59/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.59/0.58  fof(f832,plain,(
% 1.59/0.58    ( ! [X2,X1] : (r1_tarski(k1_partfun1(X1,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X2)) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.58    inference(subsumption_resolution,[],[f828,f88])).
% 1.59/0.58  fof(f88,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f3])).
% 1.59/0.58  fof(f3,axiom,(
% 1.59/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.59/0.58  fof(f828,plain,(
% 1.59/0.58    ( ! [X2,X1] : (r1_tarski(k1_partfun1(X1,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X2) | ~r1_tarski(k1_xboole_0,sK3(k1_partfun1(X1,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X2))) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.58    inference(resolution,[],[f657,f115])).
% 1.59/0.58  fof(f115,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f50])).
% 1.59/0.58  fof(f50,plain,(
% 1.59/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f16])).
% 1.59/0.58  fof(f16,axiom,(
% 1.59/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.59/0.58  fof(f657,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r2_hidden(sK3(k1_partfun1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1),k1_xboole_0) | r1_tarski(k1_partfun1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.59    inference(resolution,[],[f576,f107])).
% 1.59/0.59  fof(f107,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f71])).
% 1.59/0.59  fof(f71,plain,(
% 1.59/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f69,f70])).
% 1.59/0.59  fof(f70,plain,(
% 1.59/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f69,plain,(
% 1.59/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.59    inference(rectify,[],[f68])).
% 1.59/0.59  fof(f68,plain,(
% 1.59/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.59    inference(nnf_transformation,[],[f48])).
% 1.59/0.59  fof(f48,plain,(
% 1.59/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f1])).
% 1.59/0.59  fof(f1,axiom,(
% 1.59/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.59/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.59/0.59  fof(f576,plain,(
% 1.59/0.59    ( ! [X6,X5] : (~r2_hidden(X5,k1_partfun1(X6,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | r2_hidden(X5,k1_xboole_0)) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.59    inference(resolution,[],[f513,f101])).
% 1.59/0.59  fof(f101,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f41])).
% 1.59/0.59  fof(f41,plain,(
% 1.59/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f6])).
% 1.59/0.59  fof(f6,axiom,(
% 1.59/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.59/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.59/0.59  fof(f513,plain,(
% 1.59/0.59    ( ! [X2] : (m1_subset_1(k1_partfun1(X2,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.59    inference(subsumption_resolution,[],[f511,f312])).
% 1.59/0.59  fof(f312,plain,(
% 1.59/0.59    v1_funct_1(k1_xboole_0) | ~spl4_2),
% 1.59/0.59    inference(backward_demodulation,[],[f76,f309])).
% 1.59/0.59  fof(f76,plain,(
% 1.59/0.59    v1_funct_1(sK1)),
% 1.59/0.59    inference(cnf_transformation,[],[f66])).
% 1.59/0.59  fof(f511,plain,(
% 1.59/0.59    ( ! [X2] : (m1_subset_1(k1_partfun1(X2,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0)) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.59    inference(resolution,[],[f448,f329])).
% 1.59/0.59  fof(f329,plain,(
% 1.59/0.59    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_2 | ~spl4_5)),
% 1.59/0.59    inference(backward_demodulation,[],[f265,f309])).
% 1.59/0.59  fof(f265,plain,(
% 1.59/0.59    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl4_5),
% 1.59/0.59    inference(forward_demodulation,[],[f236,f140])).
% 1.59/0.59  fof(f140,plain,(
% 1.59/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.59/0.59    inference(equality_resolution,[],[f113])).
% 1.59/0.59  fof(f113,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.59/0.59    inference(cnf_transformation,[],[f74])).
% 1.59/0.59  fof(f74,plain,(
% 1.59/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.59/0.59    inference(flattening,[],[f73])).
% 1.59/0.59  fof(f73,plain,(
% 1.59/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.59/0.59    inference(nnf_transformation,[],[f5])).
% 1.59/0.59  fof(f5,axiom,(
% 1.59/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.59/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.59/0.59  fof(f236,plain,(
% 1.59/0.59    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_5),
% 1.59/0.59    inference(backward_demodulation,[],[f79,f219])).
% 1.59/0.59  fof(f448,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k1_partfun1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X1)) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.59    inference(superposition,[],[f334,f140])).
% 1.59/0.59  fof(f334,plain,(
% 1.59/0.59    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k1_partfun1(X1,X2,k1_xboole_0,k1_xboole_0,X3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X3)) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.59    inference(backward_demodulation,[],[f274,f309])).
% 1.59/0.59  fof(f274,plain,(
% 1.59/0.59    ( ! [X2,X3,X1] : (m1_subset_1(k1_partfun1(X1,X2,k1_xboole_0,k1_xboole_0,X3,sK1),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3)) ) | ~spl4_5),
% 1.59/0.59    inference(forward_demodulation,[],[f249,f140])).
% 1.59/0.59  fof(f249,plain,(
% 1.59/0.59    ( ! [X2,X3,X1] : (m1_subset_1(k1_partfun1(X1,X2,k1_xboole_0,k1_xboole_0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3)) ) | ~spl4_5),
% 1.59/0.59    inference(backward_demodulation,[],[f170,f219])).
% 1.59/0.59  fof(f170,plain,(
% 1.59/0.59    ( ! [X2,X3,X1] : (m1_subset_1(k1_partfun1(X1,X2,sK0,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3)) )),
% 1.59/0.59    inference(subsumption_resolution,[],[f152,f76])).
% 1.59/0.59  fof(f152,plain,(
% 1.59/0.59    ( ! [X2,X3,X1] : (m1_subset_1(k1_partfun1(X1,X2,sK0,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3)) )),
% 1.59/0.59    inference(resolution,[],[f79,f129])).
% 1.59/0.59  fof(f129,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f63])).
% 1.59/0.61  fof(f63,plain,(
% 1.59/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.59/0.61    inference(flattening,[],[f62])).
% 1.59/0.61  fof(f62,plain,(
% 1.59/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.59/0.61    inference(ennf_transformation,[],[f24])).
% 1.59/0.61  fof(f24,axiom,(
% 1.59/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.59/0.61  fof(f487,plain,(
% 1.59/0.61    ~spl4_2 | ~spl4_5 | spl4_6),
% 1.59/0.61    inference(avatar_contradiction_clause,[],[f486])).
% 1.59/0.61  fof(f486,plain,(
% 1.59/0.61    $false | (~spl4_2 | ~spl4_5 | spl4_6)),
% 1.59/0.61    inference(subsumption_resolution,[],[f484,f396])).
% 1.59/0.61  fof(f396,plain,(
% 1.59/0.61    ~m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | spl4_6),
% 1.59/0.61    inference(avatar_component_clause,[],[f394])).
% 1.59/0.61  fof(f394,plain,(
% 1.59/0.61    spl4_6 <=> m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.59/0.61  fof(f484,plain,(
% 1.59/0.61    m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(superposition,[],[f450,f130])).
% 1.59/0.61  fof(f130,plain,(
% 1.59/0.61    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.59/0.61    inference(definition_unfolding,[],[f87,f89])).
% 1.59/0.61  fof(f89,plain,(
% 1.59/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f27])).
% 1.59/0.61  fof(f27,axiom,(
% 1.59/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.59/0.61  fof(f87,plain,(
% 1.59/0.61    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.59/0.61    inference(cnf_transformation,[],[f11])).
% 1.59/0.61  fof(f11,axiom,(
% 1.59/0.61    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.59/0.61  fof(f450,plain,(
% 1.59/0.61    ( ! [X3] : (m1_subset_1(k1_partfun1(X3,X3,k1_xboole_0,k1_xboole_0,k6_partfun1(X3),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(subsumption_resolution,[],[f447,f133])).
% 1.59/0.61  fof(f133,plain,(
% 1.59/0.61    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 1.59/0.61    inference(definition_unfolding,[],[f93,f89])).
% 1.59/0.61  fof(f93,plain,(
% 1.59/0.61    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f13])).
% 1.59/0.61  fof(f13,axiom,(
% 1.59/0.61    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.59/0.61  fof(f447,plain,(
% 1.59/0.61    ( ! [X3] : (m1_subset_1(k1_partfun1(X3,X3,k1_xboole_0,k1_xboole_0,k6_partfun1(X3),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k6_partfun1(X3))) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(resolution,[],[f334,f94])).
% 1.59/0.61  fof(f94,plain,(
% 1.59/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f32])).
% 1.59/0.61  fof(f32,plain,(
% 1.59/0.61    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.59/0.61    inference(pure_predicate_removal,[],[f25])).
% 1.59/0.61  fof(f25,axiom,(
% 1.59/0.61    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.59/0.61  fof(f431,plain,(
% 1.59/0.61    ~spl4_2 | spl4_4 | ~spl4_5 | ~spl4_8),
% 1.59/0.61    inference(avatar_contradiction_clause,[],[f430])).
% 1.59/0.61  fof(f430,plain,(
% 1.59/0.61    $false | (~spl4_2 | spl4_4 | ~spl4_5 | ~spl4_8)),
% 1.59/0.61    inference(subsumption_resolution,[],[f429,f363])).
% 1.59/0.61  fof(f363,plain,(
% 1.59/0.61    k1_xboole_0 != k2_funct_1(k1_xboole_0) | (~spl4_2 | spl4_4 | ~spl4_5)),
% 1.59/0.61    inference(backward_demodulation,[],[f317,f340])).
% 1.59/0.61  fof(f340,plain,(
% 1.59/0.61    k1_xboole_0 = sK2 | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(forward_demodulation,[],[f311,f309])).
% 1.59/0.61  fof(f311,plain,(
% 1.59/0.61    sK1 = sK2 | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(resolution,[],[f283,f281])).
% 1.59/0.61  fof(f281,plain,(
% 1.59/0.61    v1_xboole_0(sK2) | ~spl4_5),
% 1.59/0.61    inference(subsumption_resolution,[],[f280,f86])).
% 1.59/0.61  fof(f280,plain,(
% 1.59/0.61    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2) | ~spl4_5),
% 1.59/0.61    inference(forward_demodulation,[],[f175,f219])).
% 1.59/0.61  fof(f175,plain,(
% 1.59/0.61    v1_xboole_0(sK2) | ~v1_xboole_0(sK0)),
% 1.59/0.61    inference(resolution,[],[f83,f99])).
% 1.59/0.61  fof(f99,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f38])).
% 1.59/0.61  fof(f38,plain,(
% 1.59/0.61    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f19])).
% 1.59/0.61  fof(f19,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.59/0.61  fof(f83,plain,(
% 1.59/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.59/0.61    inference(cnf_transformation,[],[f66])).
% 1.59/0.61  fof(f317,plain,(
% 1.59/0.61    sK2 != k2_funct_1(k1_xboole_0) | (~spl4_2 | spl4_4)),
% 1.59/0.61    inference(backward_demodulation,[],[f214,f309])).
% 1.59/0.61  fof(f214,plain,(
% 1.59/0.61    sK2 != k2_funct_1(sK1) | spl4_4),
% 1.59/0.61    inference(avatar_component_clause,[],[f213])).
% 1.59/0.61  fof(f213,plain,(
% 1.59/0.61    spl4_4 <=> sK2 = k2_funct_1(sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.59/0.61  fof(f429,plain,(
% 1.59/0.61    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl4_2 | ~spl4_5 | ~spl4_8)),
% 1.59/0.61    inference(forward_demodulation,[],[f423,f130])).
% 1.59/0.61  fof(f423,plain,(
% 1.59/0.61    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) | (~spl4_2 | ~spl4_5 | ~spl4_8)),
% 1.59/0.61    inference(backward_demodulation,[],[f389,f417])).
% 1.59/0.61  fof(f417,plain,(
% 1.59/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_8),
% 1.59/0.61    inference(avatar_component_clause,[],[f415])).
% 1.59/0.61  fof(f389,plain,(
% 1.59/0.61    k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0) | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(subsumption_resolution,[],[f388,f130])).
% 1.59/0.61  fof(f388,plain,(
% 1.59/0.61    k1_xboole_0 != k6_partfun1(k1_xboole_0) | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0) | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(forward_demodulation,[],[f387,f327])).
% 1.59/0.61  fof(f327,plain,(
% 1.59/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(backward_demodulation,[],[f263,f309])).
% 1.59/0.61  fof(f263,plain,(
% 1.59/0.61    k1_xboole_0 = k2_relat_1(sK1) | ~spl4_5),
% 1.59/0.61    inference(backward_demodulation,[],[f226,f219])).
% 1.59/0.61  fof(f226,plain,(
% 1.59/0.61    sK0 = k2_relat_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f225,f145])).
% 1.59/0.61  fof(f225,plain,(
% 1.59/0.61    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f224,f148])).
% 1.59/0.61  fof(f148,plain,(
% 1.59/0.61    v5_relat_1(sK1,sK0)),
% 1.59/0.61    inference(resolution,[],[f79,f119])).
% 1.59/0.61  fof(f119,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f53])).
% 1.59/0.61  fof(f224,plain,(
% 1.59/0.61    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.59/0.61    inference(resolution,[],[f169,f103])).
% 1.59/0.61  fof(f103,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f67])).
% 1.59/0.61  fof(f67,plain,(
% 1.59/0.61    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(nnf_transformation,[],[f45])).
% 1.59/0.61  fof(f45,plain,(
% 1.59/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(flattening,[],[f44])).
% 1.59/0.61  fof(f44,plain,(
% 1.59/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.59/0.61    inference(ennf_transformation,[],[f23])).
% 1.59/0.61  fof(f23,axiom,(
% 1.59/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.59/0.61  fof(f169,plain,(
% 1.59/0.61    v2_funct_2(sK1,sK0)),
% 1.59/0.61    inference(subsumption_resolution,[],[f168,f76])).
% 1.59/0.61  fof(f168,plain,(
% 1.59/0.61    ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 1.59/0.61    inference(subsumption_resolution,[],[f150,f78])).
% 1.59/0.61  fof(f78,plain,(
% 1.59/0.61    v3_funct_2(sK1,sK0,sK0)),
% 1.59/0.61    inference(cnf_transformation,[],[f66])).
% 1.59/0.61  fof(f150,plain,(
% 1.59/0.61    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 1.59/0.61    inference(resolution,[],[f79,f122])).
% 1.59/0.61  fof(f122,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f55])).
% 1.59/0.61  fof(f55,plain,(
% 1.59/0.61    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.61    inference(flattening,[],[f54])).
% 1.59/0.61  fof(f54,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.61    inference(ennf_transformation,[],[f22])).
% 1.59/0.61  fof(f22,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.59/0.61  fof(f387,plain,(
% 1.59/0.61    k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0)) | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0) | ~spl4_2),
% 1.59/0.61    inference(subsumption_resolution,[],[f386,f313])).
% 1.59/0.61  fof(f386,plain,(
% 1.59/0.61    k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0)) | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_2),
% 1.59/0.61    inference(subsumption_resolution,[],[f385,f312])).
% 1.59/0.61  fof(f385,plain,(
% 1.59/0.61    k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0)) | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_2),
% 1.59/0.61    inference(subsumption_resolution,[],[f384,f134])).
% 1.59/0.61  fof(f134,plain,(
% 1.59/0.61    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.59/0.61    inference(definition_unfolding,[],[f92,f89])).
% 1.59/0.61  fof(f92,plain,(
% 1.59/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f13])).
% 1.59/0.61  fof(f384,plain,(
% 1.59/0.61    k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0)) | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0) | ~v1_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_2),
% 1.59/0.61    inference(subsumption_resolution,[],[f383,f133])).
% 1.59/0.61  fof(f383,plain,(
% 1.59/0.61    k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0)) | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_relat_1(k1_xboole_0))) | ~v1_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_2),
% 1.59/0.61    inference(subsumption_resolution,[],[f382,f315])).
% 1.59/0.61  fof(f315,plain,(
% 1.59/0.61    v2_funct_1(k1_xboole_0) | ~spl4_2),
% 1.59/0.61    inference(backward_demodulation,[],[f167,f309])).
% 1.59/0.61  fof(f167,plain,(
% 1.59/0.61    v2_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f166,f76])).
% 1.59/0.61  fof(f166,plain,(
% 1.59/0.61    ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f149,f78])).
% 1.59/0.61  fof(f149,plain,(
% 1.59/0.61    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 1.59/0.61    inference(resolution,[],[f79,f121])).
% 1.59/0.61  fof(f121,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f55])).
% 1.59/0.61  fof(f382,plain,(
% 1.59/0.61    k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0)) | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_relat_1(k1_xboole_0))) | ~v1_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_2),
% 1.59/0.61    inference(subsumption_resolution,[],[f381,f135])).
% 1.59/0.61  fof(f135,plain,(
% 1.59/0.61    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.59/0.61    inference(definition_unfolding,[],[f96,f89])).
% 1.59/0.61  fof(f96,plain,(
% 1.59/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.59/0.61    inference(cnf_transformation,[],[f9])).
% 1.59/0.61  fof(f9,axiom,(
% 1.59/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.59/0.61  fof(f381,plain,(
% 1.59/0.61    k1_xboole_0 != k6_partfun1(k2_relat_1(k1_xboole_0)) | k6_partfun1(k1_relat_1(k1_xboole_0)) = k2_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != k2_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0))) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_relat_1(k1_xboole_0))) | ~v1_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_2),
% 1.59/0.61    inference(superposition,[],[f138,f316])).
% 1.59/0.61  fof(f316,plain,(
% 1.59/0.61    k1_xboole_0 = k5_relat_1(k6_partfun1(k1_relat_1(k1_xboole_0)),k1_xboole_0) | ~spl4_2),
% 1.59/0.61    inference(backward_demodulation,[],[f196,f309])).
% 1.59/0.61  fof(f196,plain,(
% 1.59/0.61    sK1 = k5_relat_1(k6_partfun1(k1_relat_1(sK1)),sK1)),
% 1.59/0.61    inference(resolution,[],[f145,f137])).
% 1.59/0.61  fof(f137,plain,(
% 1.59/0.61    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 1.59/0.61    inference(definition_unfolding,[],[f97,f89])).
% 1.59/0.61  fof(f97,plain,(
% 1.59/0.61    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f35])).
% 1.59/0.61  fof(f35,plain,(
% 1.59/0.61    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f10])).
% 1.59/0.61  fof(f10,axiom,(
% 1.59/0.61    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 1.59/0.61  fof(f138,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f98,f89])).
% 1.59/0.61  fof(f98,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f37])).
% 1.59/0.61  fof(f37,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(flattening,[],[f36])).
% 1.59/0.61  fof(f36,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f15])).
% 1.59/0.61  fof(f15,axiom,(
% 1.59/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.59/0.61  fof(f401,plain,(
% 1.59/0.61    ~spl4_6 | spl4_7 | ~spl4_2 | ~spl4_5),
% 1.59/0.61    inference(avatar_split_clause,[],[f392,f217,f162,f398,f394])).
% 1.59/0.61  fof(f392,plain,(
% 1.59/0.61    k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(resolution,[],[f337,f365])).
% 1.59/0.61  fof(f365,plain,(
% 1.59/0.61    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(backward_demodulation,[],[f330,f340])).
% 1.59/0.61  fof(f330,plain,(
% 1.59/0.61    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0) | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(backward_demodulation,[],[f267,f309])).
% 1.59/0.61  fof(f267,plain,(
% 1.59/0.61    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK2),k1_xboole_0) | ~spl4_5),
% 1.59/0.61    inference(forward_demodulation,[],[f240,f130])).
% 1.59/0.61  fof(f240,plain,(
% 1.59/0.61    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK2),k6_partfun1(k1_xboole_0)) | ~spl4_5),
% 1.59/0.61    inference(backward_demodulation,[],[f84,f219])).
% 1.59/0.61  fof(f84,plain,(
% 1.59/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.59/0.61    inference(cnf_transformation,[],[f66])).
% 1.59/0.61  fof(f337,plain,(
% 1.59/0.61    ( ! [X0] : (~r2_relset_1(k1_xboole_0,k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(forward_demodulation,[],[f331,f309])).
% 1.59/0.61  fof(f331,plain,(
% 1.59/0.61    ( ! [X0] : (k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,X0,sK1)) ) | (~spl4_2 | ~spl4_5)),
% 1.59/0.61    inference(backward_demodulation,[],[f269,f309])).
% 1.59/0.61  fof(f269,plain,(
% 1.59/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,X0,sK1) | sK1 = X0) ) | ~spl4_5),
% 1.59/0.61    inference(forward_demodulation,[],[f268,f140])).
% 1.59/0.61  fof(f268,plain,(
% 1.59/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,X0,sK1) | sK1 = X0) ) | ~spl4_5),
% 1.59/0.61    inference(forward_demodulation,[],[f243,f219])).
% 1.59/0.61  fof(f243,plain,(
% 1.59/0.61    ( ! [X0] : (~r2_relset_1(k1_xboole_0,k1_xboole_0,X0,sK1) | sK1 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ) | ~spl4_5),
% 1.59/0.61    inference(backward_demodulation,[],[f151,f219])).
% 1.59/0.61  fof(f151,plain,(
% 1.59/0.61    ( ! [X0] : (~r2_relset_1(sK0,sK0,X0,sK1) | sK1 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) )),
% 1.59/0.61    inference(resolution,[],[f79,f126])).
% 1.59/0.61  fof(f126,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f75])).
% 1.59/0.61  fof(f75,plain,(
% 1.59/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.61    inference(nnf_transformation,[],[f61])).
% 1.59/0.61  fof(f61,plain,(
% 1.59/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.61    inference(flattening,[],[f60])).
% 1.59/0.61  fof(f60,plain,(
% 1.59/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.59/0.61    inference(ennf_transformation,[],[f21])).
% 1.59/0.61  fof(f21,axiom,(
% 1.59/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.59/0.61  fof(f273,plain,(
% 1.59/0.61    spl4_1 | ~spl4_5),
% 1.59/0.61    inference(avatar_contradiction_clause,[],[f272])).
% 1.59/0.61  fof(f272,plain,(
% 1.59/0.61    $false | (spl4_1 | ~spl4_5)),
% 1.59/0.61    inference(subsumption_resolution,[],[f247,f86])).
% 1.59/0.61  fof(f247,plain,(
% 1.59/0.61    ~v1_xboole_0(k1_xboole_0) | (spl4_1 | ~spl4_5)),
% 1.59/0.61    inference(backward_demodulation,[],[f160,f219])).
% 1.59/0.61  fof(f160,plain,(
% 1.59/0.61    ~v1_xboole_0(sK0) | spl4_1),
% 1.59/0.61    inference(avatar_component_clause,[],[f158])).
% 1.59/0.61  fof(f158,plain,(
% 1.59/0.61    spl4_1 <=> v1_xboole_0(sK0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.59/0.61  fof(f233,plain,(
% 1.59/0.61    ~spl4_4),
% 1.59/0.61    inference(avatar_contradiction_clause,[],[f232])).
% 1.59/0.61  fof(f232,plain,(
% 1.59/0.61    $false | ~spl4_4),
% 1.59/0.61    inference(subsumption_resolution,[],[f230,f184])).
% 1.59/0.61  fof(f184,plain,(
% 1.59/0.61    r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.59/0.61    inference(resolution,[],[f83,f143])).
% 1.59/0.61  fof(f143,plain,(
% 1.59/0.61    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.59/0.61    inference(duplicate_literal_removal,[],[f142])).
% 1.59/0.61  fof(f142,plain,(
% 1.59/0.61    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.59/0.61    inference(equality_resolution,[],[f127])).
% 1.59/0.61  fof(f127,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f75])).
% 1.59/0.61  fof(f230,plain,(
% 1.59/0.61    ~r2_relset_1(sK0,sK0,sK2,sK2) | ~spl4_4),
% 1.59/0.61    inference(backward_demodulation,[],[f174,f215])).
% 1.59/0.61  fof(f215,plain,(
% 1.59/0.61    sK2 = k2_funct_1(sK1) | ~spl4_4),
% 1.59/0.61    inference(avatar_component_clause,[],[f213])).
% 1.59/0.61  fof(f174,plain,(
% 1.59/0.61    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 1.59/0.61    inference(backward_demodulation,[],[f85,f173])).
% 1.59/0.61  fof(f173,plain,(
% 1.59/0.61    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f172,f76])).
% 1.59/0.61  fof(f172,plain,(
% 1.59/0.61    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f171,f77])).
% 1.59/0.61  fof(f77,plain,(
% 1.59/0.61    v1_funct_2(sK1,sK0,sK0)),
% 1.59/0.61    inference(cnf_transformation,[],[f66])).
% 1.59/0.61  fof(f171,plain,(
% 1.59/0.61    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f154,f78])).
% 1.59/0.61  fof(f154,plain,(
% 1.59/0.61    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(resolution,[],[f79,f105])).
% 1.59/0.61  fof(f105,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f47])).
% 1.59/0.61  fof(f47,plain,(
% 1.59/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.59/0.61    inference(flattening,[],[f46])).
% 1.59/0.61  fof(f46,plain,(
% 1.59/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.59/0.61    inference(ennf_transformation,[],[f26])).
% 1.59/0.61  fof(f26,axiom,(
% 1.59/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.59/0.61  fof(f85,plain,(
% 1.59/0.61    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.59/0.61    inference(cnf_transformation,[],[f66])).
% 1.59/0.61  fof(f229,plain,(
% 1.59/0.61    spl4_3),
% 1.59/0.61    inference(avatar_contradiction_clause,[],[f228])).
% 1.59/0.61  fof(f228,plain,(
% 1.59/0.61    $false | spl4_3),
% 1.59/0.61    inference(subsumption_resolution,[],[f227,f211])).
% 1.59/0.61  fof(f211,plain,(
% 1.59/0.61    sK0 != k2_relset_1(sK0,sK0,sK1) | spl4_3),
% 1.59/0.61    inference(avatar_component_clause,[],[f209])).
% 1.59/0.61  fof(f209,plain,(
% 1.59/0.61    spl4_3 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.59/0.61  fof(f227,plain,(
% 1.59/0.61    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.59/0.61    inference(backward_demodulation,[],[f146,f226])).
% 1.59/0.61  fof(f146,plain,(
% 1.59/0.61    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 1.59/0.61    inference(resolution,[],[f79,f117])).
% 1.59/0.61  fof(f117,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f52])).
% 1.59/0.61  fof(f52,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.61    inference(ennf_transformation,[],[f20])).
% 1.59/0.61  fof(f20,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.59/0.61  fof(f220,plain,(
% 1.59/0.61    ~spl4_3 | spl4_4 | spl4_5),
% 1.59/0.61    inference(avatar_split_clause,[],[f207,f217,f213,f209])).
% 1.59/0.61  fof(f207,plain,(
% 1.59/0.61    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f206,f76])).
% 1.59/0.61  fof(f206,plain,(
% 1.59/0.61    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f205,f77])).
% 1.59/0.61  fof(f205,plain,(
% 1.59/0.61    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f204,f79])).
% 1.59/0.61  fof(f204,plain,(
% 1.59/0.61    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f203,f80])).
% 1.59/0.61  fof(f80,plain,(
% 1.59/0.61    v1_funct_1(sK2)),
% 1.59/0.61    inference(cnf_transformation,[],[f66])).
% 1.59/0.61  fof(f203,plain,(
% 1.59/0.61    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f202,f81])).
% 1.59/0.61  fof(f81,plain,(
% 1.59/0.61    v1_funct_2(sK2,sK0,sK0)),
% 1.59/0.61    inference(cnf_transformation,[],[f66])).
% 1.59/0.61  fof(f202,plain,(
% 1.59/0.61    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f201,f83])).
% 1.59/0.61  fof(f201,plain,(
% 1.59/0.61    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f200,f167])).
% 1.59/0.61  fof(f200,plain,(
% 1.59/0.61    k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(duplicate_literal_removal,[],[f197])).
% 1.59/0.61  fof(f197,plain,(
% 1.59/0.61    k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK2 = k2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(resolution,[],[f84,f125])).
% 1.59/0.61  fof(f125,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | k2_funct_1(X2) = X3 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f59])).
% 1.59/0.61  fof(f59,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.59/0.61    inference(flattening,[],[f58])).
% 1.59/0.61  fof(f58,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.59/0.61    inference(ennf_transformation,[],[f29])).
% 1.59/0.61  fof(f29,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.59/0.61  fof(f165,plain,(
% 1.59/0.61    ~spl4_1 | spl4_2),
% 1.59/0.61    inference(avatar_split_clause,[],[f144,f162,f158])).
% 1.59/0.61  fof(f144,plain,(
% 1.59/0.61    v1_xboole_0(sK1) | ~v1_xboole_0(sK0)),
% 1.59/0.61    inference(resolution,[],[f79,f99])).
% 1.59/0.61  % SZS output end Proof for theBenchmark
% 1.59/0.61  % (9224)------------------------------
% 1.59/0.61  % (9224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (9224)Termination reason: Refutation
% 1.59/0.61  
% 1.59/0.61  % (9224)Memory used [KB]: 11129
% 1.59/0.61  % (9224)Time elapsed: 0.189 s
% 1.59/0.61  % (9224)------------------------------
% 1.59/0.61  % (9224)------------------------------
% 1.59/0.61  % (9215)Success in time 0.253 s
%------------------------------------------------------------------------------
