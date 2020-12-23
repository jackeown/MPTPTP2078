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
% DateTime   : Thu Dec  3 13:05:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 523 expanded)
%              Number of leaves         :   24 ( 155 expanded)
%              Depth                    :   19
%              Number of atoms          :  600 (3722 expanded)
%              Number of equality atoms :  113 ( 242 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1034,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f605,f757,f803,f1033])).

fof(f1033,plain,(
    ~ spl5_29 ),
    inference(avatar_contradiction_clause,[],[f1032])).

fof(f1032,plain,
    ( $false
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f1028,f231])).

fof(f231,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f226,f160])).

fof(f160,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f141,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f141,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f83,f117])).

fof(f117,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f84,f112])).

fof(f112,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f70,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f226,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) ),
    inference(resolution,[],[f109,f70])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1028,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_29 ),
    inference(backward_demodulation,[],[f1004,f1007])).

fof(f1007,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl5_29 ),
    inference(resolution,[],[f1002,f136])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f83,f68])).

fof(f1002,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f891,f936])).

fof(f936,plain,
    ( k1_xboole_0 = sK4
    | ~ spl5_29 ),
    inference(resolution,[],[f871,f136])).

fof(f871,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f814,f106])).

fof(f814,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_29 ),
    inference(backward_demodulation,[],[f115,f604])).

fof(f604,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f602])).

fof(f602,plain,
    ( spl5_29
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f115,plain,(
    r1_tarski(sK4,k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f84,f65])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK4,sK2,sK2)
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK3,sK2,sK2)
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f46,f45])).

fof(f45,plain,
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
          ( ~ r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3))
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v3_funct_2(X2,sK2,sK2)
          & v1_funct_2(X2,sK2,sK2)
          & v1_funct_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v3_funct_2(sK3,sK2,sK2)
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3))
        & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
        & v3_funct_2(X2,sK2,sK2)
        & v1_funct_2(X2,sK2,sK2)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
      & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v3_funct_2(sK4,sK2,sK2)
      & v1_funct_2(sK4,sK2,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f891,plain,
    ( r1_tarski(k2_funct_1(sK4),k1_xboole_0)
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f843,f106])).

fof(f843,plain,
    ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_29 ),
    inference(backward_demodulation,[],[f433,f604])).

fof(f433,plain,(
    r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK2,sK2)) ),
    inference(subsumption_resolution,[],[f424,f322])).

fof(f322,plain,(
    sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f321,f62])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f321,plain,
    ( sP0(sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f320,f63])).

fof(f63,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f320,plain,
    ( sP0(sK2,sK4)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f311,f64])).

fof(f64,plain,(
    v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f311,plain,
    ( sP0(sK2,sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f80,f65])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | sP0(X0,X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(definition_folding,[],[f28,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f424,plain,
    ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK2,sK2))
    | ~ sP0(sK2,sK4) ),
    inference(superposition,[],[f193,f395])).

fof(f395,plain,(
    k2_funct_2(sK2,sK4) = k2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f394,f62])).

fof(f394,plain,
    ( k2_funct_2(sK2,sK4) = k2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f393,f63])).

fof(f393,plain,
    ( k2_funct_2(sK2,sK4) = k2_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f384,f64])).

fof(f384,plain,
    ( k2_funct_2(sK2,sK4) = k2_funct_1(sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f75,f65])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f193,plain,(
    ! [X6,X7] :
      ( r1_tarski(k2_funct_2(X6,X7),k2_zfmisc_1(X6,X6))
      | ~ sP0(X6,X7) ) ),
    inference(resolution,[],[f79,f84])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f1004,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f1003,f936])).

fof(f1003,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k2_funct_1(k1_xboole_0))
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f837,f932])).

fof(f932,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_29 ),
    inference(resolution,[],[f870,f136])).

fof(f870,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f813,f106])).

fof(f813,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_29 ),
    inference(backward_demodulation,[],[f114,f604])).

fof(f114,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f837,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k2_funct_1(sK3))
    | ~ spl5_29 ),
    inference(backward_demodulation,[],[f399,f604])).

fof(f399,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f67,f392])).

fof(f392,plain,(
    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f391,f58])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f391,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f390,f59])).

fof(f59,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f390,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f383,f60])).

fof(f60,plain,(
    v3_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f383,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v3_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f75,f61])).

fof(f67,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f803,plain,(
    ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f802])).

fof(f802,plain,
    ( $false
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f768,f225])).

fof(f225,plain,(
    r2_relset_1(sK2,sK2,sK4,sK4) ),
    inference(resolution,[],[f109,f65])).

fof(f768,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,sK4)
    | ~ spl5_21 ),
    inference(backward_demodulation,[],[f399,f499])).

fof(f499,plain,
    ( sK4 = k2_funct_1(sK3)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl5_21
  <=> sK4 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f757,plain,(
    spl5_28 ),
    inference(avatar_contradiction_clause,[],[f756])).

fof(f756,plain,
    ( $false
    | spl5_28 ),
    inference(subsumption_resolution,[],[f755,f177])).

fof(f177,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f91,f61])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f755,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | spl5_28 ),
    inference(trivial_inequality_removal,[],[f752])).

fof(f752,plain,
    ( sK2 != sK2
    | ~ v5_relat_1(sK3,sK2)
    | spl5_28 ),
    inference(resolution,[],[f609,f307])).

fof(f307,plain,(
    v2_funct_2(sK3,sK2) ),
    inference(resolution,[],[f302,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f302,plain,(
    sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f301,f58])).

fof(f301,plain,
    ( ~ v1_funct_1(sK3)
    | sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f294,f60])).

fof(f294,plain,
    ( ~ v3_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3)
    | sP1(sK2,sK3) ),
    inference(resolution,[],[f95,f61])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | sP1(X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f32,f43])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f609,plain,
    ( ! [X0] :
        ( ~ v2_funct_2(sK3,X0)
        | sK2 != X0
        | ~ v5_relat_1(sK3,X0) )
    | spl5_28 ),
    inference(subsumption_resolution,[],[f608,f126])).

fof(f126,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f121,f72])).

fof(f72,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f121,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f71,f61])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f608,plain,
    ( ! [X0] :
        ( sK2 != X0
        | ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl5_28 ),
    inference(superposition,[],[f607,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f607,plain,
    ( sK2 != k2_relat_1(sK3)
    | spl5_28 ),
    inference(subsumption_resolution,[],[f606,f61])).

fof(f606,plain,
    ( sK2 != k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | spl5_28 ),
    inference(superposition,[],[f600,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f600,plain,
    ( sK2 != k2_relset_1(sK2,sK2,sK3)
    | spl5_28 ),
    inference(avatar_component_clause,[],[f598])).

fof(f598,plain,
    ( spl5_28
  <=> sK2 = k2_relset_1(sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f605,plain,
    ( ~ spl5_28
    | spl5_21
    | spl5_29 ),
    inference(avatar_split_clause,[],[f596,f602,f497,f598])).

fof(f596,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3) ),
    inference(subsumption_resolution,[],[f595,f58])).

fof(f595,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f594,f59])).

fof(f594,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f593,f61])).

fof(f593,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f592,f62])).

fof(f592,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f591,f63])).

fof(f591,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f590,f65])).

fof(f590,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(duplicate_literal_removal,[],[f588])).

fof(f588,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | sK4 = k2_funct_1(sK3)
    | sK2 != k2_relset_1(sK2,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f569,f66])).

fof(f66,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f569,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_funct_1(X2) = X3
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f98,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (20705)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.46  % (20697)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % (20690)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (20708)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.49  % (20698)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (20700)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (20691)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (20692)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (20706)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (20701)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (20694)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (20686)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (20699)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (20688)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (20704)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (20689)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (20707)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (20693)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (20710)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (20687)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (20711)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (20695)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (20696)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (20690)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f1034,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f605,f757,f803,f1033])).
% 0.20/0.53  fof(f1033,plain,(
% 0.20/0.53    ~spl5_29),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f1032])).
% 0.20/0.53  fof(f1032,plain,(
% 0.20/0.53    $false | ~spl5_29),
% 0.20/0.53    inference(subsumption_resolution,[],[f1028,f231])).
% 0.20/0.53  fof(f231,plain,(
% 0.20/0.53    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    inference(superposition,[],[f226,f160])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f141,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0))),
% 0.20/0.53    inference(resolution,[],[f83,f117])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f84,f112])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.53    inference(superposition,[],[f70,f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(flattening,[],[f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    ( ! [X0] : (r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))) )),
% 0.20/0.53    inference(resolution,[],[f109,f70])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(equality_resolution,[],[f100])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.53  fof(f1028,plain,(
% 0.20/0.53    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl5_29),
% 0.20/0.53    inference(backward_demodulation,[],[f1004,f1007])).
% 0.20/0.53  fof(f1007,plain,(
% 0.20/0.53    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl5_29),
% 0.20/0.53    inference(resolution,[],[f1002,f136])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(resolution,[],[f83,f68])).
% 0.20/0.53  fof(f1002,plain,(
% 0.20/0.53    r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) | ~spl5_29),
% 0.20/0.53    inference(forward_demodulation,[],[f891,f936])).
% 0.20/0.53  fof(f936,plain,(
% 0.20/0.53    k1_xboole_0 = sK4 | ~spl5_29),
% 0.20/0.53    inference(resolution,[],[f871,f136])).
% 0.20/0.53  fof(f871,plain,(
% 0.20/0.53    r1_tarski(sK4,k1_xboole_0) | ~spl5_29),
% 0.20/0.53    inference(forward_demodulation,[],[f814,f106])).
% 0.20/0.53  fof(f814,plain,(
% 0.20/0.53    r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | ~spl5_29),
% 0.20/0.53    inference(backward_demodulation,[],[f115,f604])).
% 0.20/0.53  fof(f604,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | ~spl5_29),
% 0.20/0.53    inference(avatar_component_clause,[],[f602])).
% 0.20/0.53  fof(f602,plain,(
% 0.20/0.53    spl5_29 <=> k1_xboole_0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    r1_tarski(sK4,k2_zfmisc_1(sK2,sK2))),
% 0.20/0.53    inference(resolution,[],[f84,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    (~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f46,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(X2,sK2,sK2) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ? [X2] : (~r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(X2,sK2,sK2) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) => (~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f18])).
% 0.20/0.53  fof(f18,conjecture,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 0.20/0.53  fof(f891,plain,(
% 0.20/0.53    r1_tarski(k2_funct_1(sK4),k1_xboole_0) | ~spl5_29),
% 0.20/0.53    inference(forward_demodulation,[],[f843,f106])).
% 0.20/0.53  fof(f843,plain,(
% 0.20/0.53    r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | ~spl5_29),
% 0.20/0.53    inference(backward_demodulation,[],[f433,f604])).
% 0.20/0.53  fof(f433,plain,(
% 0.20/0.53    r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK2,sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f424,f322])).
% 0.20/0.53  fof(f322,plain,(
% 0.20/0.53    sP0(sK2,sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f321,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    v1_funct_1(sK4)),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f321,plain,(
% 0.20/0.53    sP0(sK2,sK4) | ~v1_funct_1(sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f320,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    v1_funct_2(sK4,sK2,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f320,plain,(
% 0.20/0.53    sP0(sK2,sK4) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f311,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    v3_funct_2(sK4,sK2,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f311,plain,(
% 0.20/0.53    sP0(sK2,sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.20/0.53    inference(resolution,[],[f80,f65])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | sP0(X0,X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.53    inference(definition_folding,[],[f28,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.53    inference(flattening,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.20/0.53  fof(f424,plain,(
% 0.20/0.53    r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK2,sK2)) | ~sP0(sK2,sK4)),
% 0.20/0.53    inference(superposition,[],[f193,f395])).
% 0.20/0.53  fof(f395,plain,(
% 0.20/0.53    k2_funct_2(sK2,sK4) = k2_funct_1(sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f394,f62])).
% 0.20/0.53  fof(f394,plain,(
% 0.20/0.53    k2_funct_2(sK2,sK4) = k2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f393,f63])).
% 0.20/0.53  fof(f393,plain,(
% 0.20/0.53    k2_funct_2(sK2,sK4) = k2_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f384,f64])).
% 0.20/0.53  fof(f384,plain,(
% 0.20/0.53    k2_funct_2(sK2,sK4) = k2_funct_1(sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.20/0.53    inference(resolution,[],[f75,f65])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.53    inference(flattening,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    ( ! [X6,X7] : (r1_tarski(k2_funct_2(X6,X7),k2_zfmisc_1(X6,X6)) | ~sP0(X6,X7)) )),
% 0.20/0.53    inference(resolution,[],[f79,f84])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~sP0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f41])).
% 0.20/0.53  fof(f1004,plain,(
% 0.20/0.53    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) | ~spl5_29),
% 0.20/0.53    inference(forward_demodulation,[],[f1003,f936])).
% 0.20/0.53  fof(f1003,plain,(
% 0.20/0.53    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k2_funct_1(k1_xboole_0)) | ~spl5_29),
% 0.20/0.53    inference(forward_demodulation,[],[f837,f932])).
% 0.20/0.53  fof(f932,plain,(
% 0.20/0.53    k1_xboole_0 = sK3 | ~spl5_29),
% 0.20/0.53    inference(resolution,[],[f870,f136])).
% 0.20/0.53  fof(f870,plain,(
% 0.20/0.53    r1_tarski(sK3,k1_xboole_0) | ~spl5_29),
% 0.20/0.53    inference(forward_demodulation,[],[f813,f106])).
% 0.20/0.53  fof(f813,plain,(
% 0.20/0.53    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | ~spl5_29),
% 0.20/0.53    inference(backward_demodulation,[],[f114,f604])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    r1_tarski(sK3,k2_zfmisc_1(sK2,sK2))),
% 0.20/0.53    inference(resolution,[],[f84,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f837,plain,(
% 0.20/0.53    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k2_funct_1(sK3)) | ~spl5_29),
% 0.20/0.53    inference(backward_demodulation,[],[f399,f604])).
% 0.20/0.53  fof(f399,plain,(
% 0.20/0.53    ~r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3))),
% 0.20/0.53    inference(backward_demodulation,[],[f67,f392])).
% 0.20/0.53  fof(f392,plain,(
% 0.20/0.53    k2_funct_2(sK2,sK3) = k2_funct_1(sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f391,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f391,plain,(
% 0.20/0.53    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f390,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK2,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f390,plain,(
% 0.20/0.53    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f383,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    v3_funct_2(sK3,sK2,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f383,plain,(
% 0.20/0.53    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v3_funct_2(sK3,sK2,sK2) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(resolution,[],[f75,f61])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f803,plain,(
% 0.20/0.53    ~spl5_21),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f802])).
% 0.20/0.53  fof(f802,plain,(
% 0.20/0.53    $false | ~spl5_21),
% 0.20/0.53    inference(subsumption_resolution,[],[f768,f225])).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    r2_relset_1(sK2,sK2,sK4,sK4)),
% 0.20/0.53    inference(resolution,[],[f109,f65])).
% 0.20/0.53  fof(f768,plain,(
% 0.20/0.53    ~r2_relset_1(sK2,sK2,sK4,sK4) | ~spl5_21),
% 0.20/0.53    inference(backward_demodulation,[],[f399,f499])).
% 0.20/0.53  fof(f499,plain,(
% 0.20/0.53    sK4 = k2_funct_1(sK3) | ~spl5_21),
% 0.20/0.53    inference(avatar_component_clause,[],[f497])).
% 0.20/0.53  fof(f497,plain,(
% 0.20/0.53    spl5_21 <=> sK4 = k2_funct_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.53  fof(f757,plain,(
% 0.20/0.53    spl5_28),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f756])).
% 0.20/0.53  fof(f756,plain,(
% 0.20/0.53    $false | spl5_28),
% 0.20/0.53    inference(subsumption_resolution,[],[f755,f177])).
% 0.20/0.53  fof(f177,plain,(
% 0.20/0.53    v5_relat_1(sK3,sK2)),
% 0.20/0.53    inference(resolution,[],[f91,f61])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f755,plain,(
% 0.20/0.53    ~v5_relat_1(sK3,sK2) | spl5_28),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f752])).
% 0.20/0.53  fof(f752,plain,(
% 0.20/0.53    sK2 != sK2 | ~v5_relat_1(sK3,sK2) | spl5_28),
% 0.20/0.53    inference(resolution,[],[f609,f307])).
% 0.20/0.53  fof(f307,plain,(
% 0.20/0.53    v2_funct_2(sK3,sK2)),
% 0.20/0.53    inference(resolution,[],[f302,f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~sP1(X0,X1) | v2_funct_2(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) & v2_funct_1(X1) & v1_funct_1(X1)) | ~sP1(X0,X1))),
% 0.20/0.53    inference(rectify,[],[f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.53  fof(f302,plain,(
% 0.20/0.53    sP1(sK2,sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f301,f58])).
% 0.20/0.53  fof(f301,plain,(
% 0.20/0.53    ~v1_funct_1(sK3) | sP1(sK2,sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f294,f60])).
% 0.20/0.53  fof(f294,plain,(
% 0.20/0.53    ~v3_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3) | sP1(sK2,sK3)),
% 0.20/0.53    inference(resolution,[],[f95,f61])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | sP1(X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (sP1(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(definition_folding,[],[f32,f43])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.20/0.53  fof(f609,plain,(
% 0.20/0.53    ( ! [X0] : (~v2_funct_2(sK3,X0) | sK2 != X0 | ~v5_relat_1(sK3,X0)) ) | spl5_28),
% 0.20/0.53    inference(subsumption_resolution,[],[f608,f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    v1_relat_1(sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f121,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 0.20/0.53    inference(resolution,[],[f71,f61])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.53  fof(f608,plain,(
% 0.20/0.53    ( ! [X0] : (sK2 != X0 | ~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl5_28),
% 0.20/0.53    inference(superposition,[],[f607,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.20/0.53  fof(f607,plain,(
% 0.20/0.53    sK2 != k2_relat_1(sK3) | spl5_28),
% 0.20/0.53    inference(subsumption_resolution,[],[f606,f61])).
% 0.20/0.53  fof(f606,plain,(
% 0.20/0.53    sK2 != k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | spl5_28),
% 0.20/0.53    inference(superposition,[],[f600,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.53  fof(f600,plain,(
% 0.20/0.53    sK2 != k2_relset_1(sK2,sK2,sK3) | spl5_28),
% 0.20/0.53    inference(avatar_component_clause,[],[f598])).
% 0.20/0.53  fof(f598,plain,(
% 0.20/0.53    spl5_28 <=> sK2 = k2_relset_1(sK2,sK2,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.20/0.53  fof(f605,plain,(
% 0.20/0.53    ~spl5_28 | spl5_21 | spl5_29),
% 0.20/0.53    inference(avatar_split_clause,[],[f596,f602,f497,f598])).
% 0.20/0.53  fof(f596,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f595,f58])).
% 0.20/0.53  fof(f595,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f594,f59])).
% 0.20/0.53  fof(f594,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f593,f61])).
% 0.20/0.53  fof(f593,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f592,f62])).
% 0.20/0.53  fof(f592,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f591,f63])).
% 0.20/0.53  fof(f591,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f590,f65])).
% 0.20/0.53  fof(f590,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f588])).
% 0.20/0.53  fof(f588,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | sK4 = k2_funct_1(sK3) | sK2 != k2_relset_1(sK2,sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(resolution,[],[f569,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f569,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_funct_1(X2) = X3 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f98,f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (20690)------------------------------
% 0.20/0.53  % (20690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20690)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (20690)Memory used [KB]: 6524
% 0.20/0.53  % (20690)Time elapsed: 0.130 s
% 0.20/0.53  % (20690)------------------------------
% 0.20/0.53  % (20690)------------------------------
% 0.20/0.53  % (20685)Success in time 0.181 s
%------------------------------------------------------------------------------
