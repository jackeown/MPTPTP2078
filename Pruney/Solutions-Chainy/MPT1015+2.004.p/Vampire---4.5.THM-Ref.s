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
% DateTime   : Thu Dec  3 13:05:25 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 489 expanded)
%              Number of leaves         :   27 ( 151 expanded)
%              Depth                    :   29
%              Number of atoms          :  583 (3239 expanded)
%              Number of equality atoms :  173 ( 267 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1544,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f397,f400,f1177,f1181,f1249,f1454,f1543])).

fof(f1543,plain,
    ( ~ spl4_6
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f1542])).

fof(f1542,plain,
    ( $false
    | ~ spl4_6
    | spl4_20 ),
    inference(subsumption_resolution,[],[f1541,f378])).

fof(f378,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f359,f112])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f359,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f123,f343])).

fof(f343,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f123,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK1)) ),
    inference(resolution,[],[f81,f62])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1))
    & v2_funct_1(sK2)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK3,sK1,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK1,sK1,X2,k6_partfun1(sK1))
          & v2_funct_1(sK2)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,X2,sK2),sK2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v1_funct_2(X2,sK1,sK1)
          & v1_funct_1(X2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK1,sK1,X2,k6_partfun1(sK1))
        & v2_funct_1(sK2)
        & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,X2,sK2),sK2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
        & v1_funct_2(X2,sK1,sK1)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1))
      & v2_funct_1(sK2)
      & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v1_funct_2(sK3,sK1,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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

fof(f1541,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl4_20 ),
    inference(subsumption_resolution,[],[f1520,f121])).

fof(f121,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f81,f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1520,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ r1_tarski(sK3,k1_xboole_0)
    | spl4_20 ),
    inference(extensionality_resolution,[],[f80,f652])).

fof(f652,plain,
    ( k1_xboole_0 != sK3
    | spl4_20 ),
    inference(avatar_component_clause,[],[f651])).

fof(f651,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f1454,plain,
    ( ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f1453])).

fof(f1453,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f1452,f264])).

fof(f264,plain,(
    ! [X4,X3] : r2_relset_1(X3,X4,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f120,f66])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1452,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f376,f653])).

fof(f653,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f651])).

fof(f376,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k1_xboole_0)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f357,f157])).

fof(f157,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(equality_resolution,[],[f142])).

fof(f142,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0) ) ),
    inference(subsumption_resolution,[],[f141,f105])).

fof(f105,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f69,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f141,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f73,f107])).

fof(f107,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f67])).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f357,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k6_partfun1(k1_xboole_0))
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f65,f343])).

fof(f65,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f1249,plain,(
    ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f1248])).

fof(f1248,plain,
    ( $false
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f1224,f267])).

fof(f267,plain,(
    r2_relset_1(sK1,sK1,sK3,sK3) ),
    inference(resolution,[],[f120,f62])).

fof(f1224,plain,
    ( ~ r2_relset_1(sK1,sK1,sK3,sK3)
    | ~ spl4_22 ),
    inference(backward_demodulation,[],[f65,f662])).

fof(f662,plain,
    ( k6_partfun1(sK1) = sK3
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f660])).

fof(f660,plain,
    ( spl4_22
  <=> k6_partfun1(sK1) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f1181,plain,(
    spl4_44 ),
    inference(avatar_contradiction_clause,[],[f1180])).

fof(f1180,plain,
    ( $false
    | spl4_44 ),
    inference(subsumption_resolution,[],[f1179,f133])).

fof(f133,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f86,f62])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1179,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_44 ),
    inference(subsumption_resolution,[],[f1178,f235])).

fof(f235,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f89,f62])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1178,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | spl4_44 ),
    inference(resolution,[],[f1176,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f1176,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | spl4_44 ),
    inference(avatar_component_clause,[],[f1174])).

fof(f1174,plain,
    ( spl4_44
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f1177,plain,
    ( spl4_22
    | ~ spl4_44
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f1172,f347,f337,f1174,f660])).

fof(f337,plain,
    ( spl4_5
  <=> sK1 = k1_relset_1(sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f347,plain,
    ( spl4_7
  <=> sK1 = k1_relset_1(sK1,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1172,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | k6_partfun1(sK1) = sK3
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1171,f459])).

fof(f459,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f273,f339])).

fof(f339,plain,
    ( sK1 = k1_relset_1(sK1,sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f337])).

fof(f273,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK1,sK1,sK2) ),
    inference(resolution,[],[f87,f59])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1171,plain,
    ( sK1 != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK3),sK1)
    | k6_partfun1(sK1) = sK3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1170,f492])).

fof(f492,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f274,f349])).

fof(f349,plain,
    ( sK1 = k1_relset_1(sK1,sK1,sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f347])).

fof(f274,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK1,sK3) ),
    inference(resolution,[],[f87,f62])).

fof(f1170,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | k6_partfun1(sK1) = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1169,f492])).

fof(f1169,plain,
    ( k6_partfun1(sK1) = sK3
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3))
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1168,f492])).

fof(f1168,plain,
    ( sK3 = k6_partfun1(k1_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3))
    | k1_relat_1(sK2) != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1167,f132])).

fof(f132,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f86,f59])).

fof(f1167,plain,
    ( sK3 = k6_partfun1(k1_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3))
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1166,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f1166,plain,
    ( sK3 = k6_partfun1(k1_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3))
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1165,f133])).

fof(f1165,plain,
    ( sK3 = k6_partfun1(k1_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3))
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1164,f60])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f1164,plain,
    ( sK3 = k6_partfun1(k1_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3))
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1163,f64])).

fof(f64,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f1163,plain,
    ( sK3 = k6_partfun1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3))
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f1162])).

fof(f1162,plain,
    ( sK2 != sK2
    | sK3 = k6_partfun1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3))
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f109,f1131])).

fof(f1131,plain,(
    sK2 = k5_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f1108,f1078])).

fof(f1078,plain,(
    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),sK2) ),
    inference(backward_demodulation,[],[f63,f869])).

fof(f869,plain,(
    k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f864,f60])).

fof(f864,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f490,f62])).

fof(f490,plain,(
    ! [X17,X15,X16] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k1_partfun1(X15,X16,sK1,sK1,X17,sK2) = k5_relat_1(X17,sK2)
      | ~ v1_funct_1(X17) ) ),
    inference(subsumption_resolution,[],[f478,f57])).

fof(f478,plain,(
    ! [X17,X15,X16] :
      ( k1_partfun1(X15,X16,sK1,sK1,X17,sK2) = k5_relat_1(X17,sK2)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | ~ v1_funct_1(X17) ) ),
    inference(resolution,[],[f100,f59])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f63,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2),sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f1108,plain,
    ( sK2 = k5_relat_1(sK3,sK2)
    | ~ r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),sK2) ),
    inference(resolution,[],[f1084,f443])).

fof(f443,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      | sK2 = X9
      | ~ r2_relset_1(sK1,sK1,X9,sK2) ) ),
    inference(resolution,[],[f98,f59])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1084,plain,(
    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f1083,f60])).

fof(f1083,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1082,f62])).

fof(f1082,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1081,f57])).

fof(f1081,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1079,f59])).

fof(f1079,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f102,f869])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f109,plain,(
    ! [X2,X1] :
      ( k5_relat_1(X2,X1) != X1
      | k6_partfun1(k1_relat_1(X2)) = X2
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X2))
      | k1_relat_1(X1) != k1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = X2
      | k5_relat_1(X2,X1) != X1
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | k1_relat_1(X2) != X0
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f67])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k6_relat_1(X0) = X2
      | k5_relat_1(X2,X1) != X1
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | k1_relat_1(X2) != X0
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k6_relat_1(X0) = X2
          | k5_relat_1(X2,X1) != X1
          | ~ v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X0
          | k1_relat_1(X1) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k6_relat_1(X0) = X2
          | k5_relat_1(X2,X1) != X1
          | ~ v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X0
          | k1_relat_1(X1) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

fof(f400,plain,
    ( spl4_7
    | spl4_6 ),
    inference(avatar_split_clause,[],[f399,f341,f347])).

fof(f399,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_relset_1(sK1,sK1,sK3) ),
    inference(subsumption_resolution,[],[f398,f61])).

fof(f61,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f398,plain,
    ( ~ v1_funct_2(sK3,sK1,sK1)
    | k1_xboole_0 = sK1
    | sK1 = k1_relset_1(sK1,sK1,sK3) ),
    inference(resolution,[],[f243,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f243,plain,(
    sP0(sK1,sK3,sK1) ),
    inference(resolution,[],[f94,f62])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f33,f42])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f397,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f396,f341,f337])).

fof(f396,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_relset_1(sK1,sK1,sK2) ),
    inference(subsumption_resolution,[],[f395,f58])).

fof(f58,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f395,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | k1_xboole_0 = sK1
    | sK1 = k1_relset_1(sK1,sK1,sK2) ),
    inference(resolution,[],[f242,f90])).

fof(f242,plain,(
    sP0(sK1,sK2,sK1) ),
    inference(resolution,[],[f94,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.37/0.55  % (15917)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.37/0.56  % (15901)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.57  % (15914)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.56/0.57  % (15897)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.56/0.57  % (15908)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.56/0.58  % (15909)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.56/0.58  % (15907)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.56/0.58  % (15898)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.56/0.58  % (15922)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.56/0.58  % (15895)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.56/0.59  % (15899)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.56/0.59  % (15905)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.56/0.59  % (15900)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.56/0.59  % (15918)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.56/0.59  % (15912)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.56/0.60  % (15910)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.56/0.60  % (15921)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.56/0.60  % (15916)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.56/0.61  % (15923)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.56/0.61  % (15906)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.56/0.61  % (15902)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.56/0.61  % (15896)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.56/0.62  % (15913)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.56/0.62  % (15919)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.56/0.62  % (15903)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.56/0.63  % (15920)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.56/0.63  % (15904)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.56/0.63  % (15911)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.56/0.64  % (15915)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.56/0.64  % (15911)Refutation not found, incomplete strategy% (15911)------------------------------
% 1.56/0.64  % (15911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.64  % (15911)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.64  
% 1.56/0.64  % (15911)Memory used [KB]: 10746
% 1.56/0.64  % (15911)Time elapsed: 0.210 s
% 1.56/0.64  % (15911)------------------------------
% 1.56/0.64  % (15911)------------------------------
% 1.56/0.64  % (15901)Refutation found. Thanks to Tanya!
% 1.56/0.64  % SZS status Theorem for theBenchmark
% 2.18/0.64  % (15924)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 2.18/0.64  % SZS output start Proof for theBenchmark
% 2.18/0.65  fof(f1544,plain,(
% 2.18/0.65    $false),
% 2.18/0.65    inference(avatar_sat_refutation,[],[f397,f400,f1177,f1181,f1249,f1454,f1543])).
% 2.18/0.65  fof(f1543,plain,(
% 2.18/0.65    ~spl4_6 | spl4_20),
% 2.18/0.65    inference(avatar_contradiction_clause,[],[f1542])).
% 2.18/0.65  fof(f1542,plain,(
% 2.18/0.65    $false | (~spl4_6 | spl4_20)),
% 2.18/0.65    inference(subsumption_resolution,[],[f1541,f378])).
% 2.18/0.65  fof(f378,plain,(
% 2.18/0.65    r1_tarski(sK3,k1_xboole_0) | ~spl4_6),
% 2.18/0.65    inference(forward_demodulation,[],[f359,f112])).
% 2.18/0.65  fof(f112,plain,(
% 2.18/0.65    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.18/0.65    inference(equality_resolution,[],[f85])).
% 2.18/0.65  fof(f85,plain,(
% 2.18/0.65    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.18/0.65    inference(cnf_transformation,[],[f52])).
% 2.18/0.65  fof(f52,plain,(
% 2.18/0.65    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.18/0.65    inference(flattening,[],[f51])).
% 2.18/0.65  fof(f51,plain,(
% 2.18/0.65    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.18/0.65    inference(nnf_transformation,[],[f2])).
% 2.18/0.65  fof(f2,axiom,(
% 2.18/0.65    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.18/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.18/0.65  fof(f359,plain,(
% 2.18/0.65    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | ~spl4_6),
% 2.18/0.65    inference(backward_demodulation,[],[f123,f343])).
% 2.18/0.65  fof(f343,plain,(
% 2.18/0.65    k1_xboole_0 = sK1 | ~spl4_6),
% 2.18/0.65    inference(avatar_component_clause,[],[f341])).
% 2.18/0.65  fof(f341,plain,(
% 2.18/0.65    spl4_6 <=> k1_xboole_0 = sK1),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.18/0.65  fof(f123,plain,(
% 2.18/0.65    r1_tarski(sK3,k2_zfmisc_1(sK1,sK1))),
% 2.18/0.65    inference(resolution,[],[f81,f62])).
% 2.18/0.65  fof(f62,plain,(
% 2.18/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.18/0.65    inference(cnf_transformation,[],[f46])).
% 2.18/0.65  fof(f46,plain,(
% 2.18/0.65    (~r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1)) & v2_funct_1(sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 2.18/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f45,f44])).
% 2.18/0.65  fof(f44,plain,(
% 2.18/0.65    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK1,sK1,X2,k6_partfun1(sK1)) & v2_funct_1(sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,X2,sK2),sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 2.18/0.65    introduced(choice_axiom,[])).
% 2.18/0.65  fof(f45,plain,(
% 2.18/0.65    ? [X2] : (~r2_relset_1(sK1,sK1,X2,k6_partfun1(sK1)) & v2_funct_1(sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,X2,sK2),sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) => (~r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1)) & v2_funct_1(sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3))),
% 2.18/0.65    introduced(choice_axiom,[])).
% 2.18/0.65  fof(f23,plain,(
% 2.18/0.65    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.18/0.65    inference(flattening,[],[f22])).
% 2.18/0.66  fof(f22,plain,(
% 2.18/0.66    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.18/0.66    inference(ennf_transformation,[],[f21])).
% 2.18/0.66  fof(f21,negated_conjecture,(
% 2.18/0.66    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 2.18/0.66    inference(negated_conjecture,[],[f20])).
% 2.18/0.66  fof(f20,conjecture,(
% 2.18/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).
% 2.18/0.66  fof(f81,plain,(
% 2.18/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f50])).
% 2.18/0.66  fof(f50,plain,(
% 2.18/0.66    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.18/0.66    inference(nnf_transformation,[],[f4])).
% 2.18/0.66  fof(f4,axiom,(
% 2.18/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.18/0.66  fof(f1541,plain,(
% 2.18/0.66    ~r1_tarski(sK3,k1_xboole_0) | spl4_20),
% 2.18/0.66    inference(subsumption_resolution,[],[f1520,f121])).
% 2.18/0.66  fof(f121,plain,(
% 2.18/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.18/0.66    inference(resolution,[],[f81,f66])).
% 2.18/0.66  fof(f66,plain,(
% 2.18/0.66    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f3])).
% 2.18/0.66  fof(f3,axiom,(
% 2.18/0.66    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.18/0.66  fof(f1520,plain,(
% 2.18/0.66    ~r1_tarski(k1_xboole_0,sK3) | ~r1_tarski(sK3,k1_xboole_0) | spl4_20),
% 2.18/0.66    inference(extensionality_resolution,[],[f80,f652])).
% 2.18/0.66  fof(f652,plain,(
% 2.18/0.66    k1_xboole_0 != sK3 | spl4_20),
% 2.18/0.66    inference(avatar_component_clause,[],[f651])).
% 2.18/0.66  fof(f651,plain,(
% 2.18/0.66    spl4_20 <=> k1_xboole_0 = sK3),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.18/0.66  fof(f80,plain,(
% 2.18/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f49])).
% 2.18/0.66  fof(f49,plain,(
% 2.18/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/0.66    inference(flattening,[],[f48])).
% 2.18/0.66  fof(f48,plain,(
% 2.18/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/0.66    inference(nnf_transformation,[],[f1])).
% 2.18/0.66  fof(f1,axiom,(
% 2.18/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.18/0.66  fof(f1454,plain,(
% 2.18/0.66    ~spl4_6 | ~spl4_20),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f1453])).
% 2.18/0.66  fof(f1453,plain,(
% 2.18/0.66    $false | (~spl4_6 | ~spl4_20)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1452,f264])).
% 2.18/0.66  fof(f264,plain,(
% 2.18/0.66    ( ! [X4,X3] : (r2_relset_1(X3,X4,k1_xboole_0,k1_xboole_0)) )),
% 2.18/0.66    inference(resolution,[],[f120,f66])).
% 2.18/0.66  fof(f120,plain,(
% 2.18/0.66    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 2.18/0.66    inference(duplicate_literal_removal,[],[f119])).
% 2.18/0.66  fof(f119,plain,(
% 2.18/0.66    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.66    inference(equality_resolution,[],[f99])).
% 2.18/0.66  fof(f99,plain,(
% 2.18/0.66    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f56])).
% 2.18/0.66  fof(f56,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.66    inference(nnf_transformation,[],[f37])).
% 2.18/0.66  fof(f37,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.66    inference(flattening,[],[f36])).
% 2.18/0.66  fof(f36,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.18/0.66    inference(ennf_transformation,[],[f14])).
% 2.18/0.66  fof(f14,axiom,(
% 2.18/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.18/0.66  fof(f1452,plain,(
% 2.18/0.66    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_6 | ~spl4_20)),
% 2.18/0.66    inference(forward_demodulation,[],[f376,f653])).
% 2.18/0.66  fof(f653,plain,(
% 2.18/0.66    k1_xboole_0 = sK3 | ~spl4_20),
% 2.18/0.66    inference(avatar_component_clause,[],[f651])).
% 2.18/0.66  fof(f376,plain,(
% 2.18/0.66    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k1_xboole_0) | ~spl4_6),
% 2.18/0.66    inference(forward_demodulation,[],[f357,f157])).
% 2.18/0.66  fof(f157,plain,(
% 2.18/0.66    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.18/0.66    inference(equality_resolution,[],[f142])).
% 2.18/0.66  fof(f142,plain,(
% 2.18/0.66    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0)) )),
% 2.18/0.66    inference(subsumption_resolution,[],[f141,f105])).
% 2.18/0.66  fof(f105,plain,(
% 2.18/0.66    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.18/0.66    inference(definition_unfolding,[],[f69,f67])).
% 2.18/0.66  fof(f67,plain,(
% 2.18/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f19])).
% 2.18/0.66  fof(f19,axiom,(
% 2.18/0.66    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.18/0.66  fof(f69,plain,(
% 2.18/0.66    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f9])).
% 2.18/0.66  fof(f9,axiom,(
% 2.18/0.66    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.18/0.66  fof(f141,plain,(
% 2.18/0.66    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0) | ~v1_relat_1(k6_partfun1(X0))) )),
% 2.18/0.66    inference(superposition,[],[f73,f107])).
% 2.18/0.66  fof(f107,plain,(
% 2.18/0.66    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.18/0.66    inference(definition_unfolding,[],[f71,f67])).
% 2.18/0.66  fof(f71,plain,(
% 2.18/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.18/0.66    inference(cnf_transformation,[],[f8])).
% 2.18/0.66  fof(f8,axiom,(
% 2.18/0.66    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.18/0.66  fof(f73,plain,(
% 2.18/0.66    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f25])).
% 2.18/0.66  fof(f25,plain,(
% 2.18/0.66    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.18/0.66    inference(flattening,[],[f24])).
% 2.18/0.66  fof(f24,plain,(
% 2.18/0.66    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.18/0.66    inference(ennf_transformation,[],[f7])).
% 2.18/0.66  fof(f7,axiom,(
% 2.18/0.66    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 2.18/0.66  fof(f357,plain,(
% 2.18/0.66    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k6_partfun1(k1_xboole_0)) | ~spl4_6),
% 2.18/0.66    inference(backward_demodulation,[],[f65,f343])).
% 2.18/0.66  fof(f65,plain,(
% 2.18/0.66    ~r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1))),
% 2.18/0.66    inference(cnf_transformation,[],[f46])).
% 2.18/0.66  fof(f1249,plain,(
% 2.18/0.66    ~spl4_22),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f1248])).
% 2.18/0.66  fof(f1248,plain,(
% 2.18/0.66    $false | ~spl4_22),
% 2.18/0.66    inference(subsumption_resolution,[],[f1224,f267])).
% 2.18/0.66  fof(f267,plain,(
% 2.18/0.66    r2_relset_1(sK1,sK1,sK3,sK3)),
% 2.18/0.66    inference(resolution,[],[f120,f62])).
% 2.18/0.66  fof(f1224,plain,(
% 2.18/0.66    ~r2_relset_1(sK1,sK1,sK3,sK3) | ~spl4_22),
% 2.18/0.66    inference(backward_demodulation,[],[f65,f662])).
% 2.18/0.66  fof(f662,plain,(
% 2.18/0.66    k6_partfun1(sK1) = sK3 | ~spl4_22),
% 2.18/0.66    inference(avatar_component_clause,[],[f660])).
% 2.18/0.66  fof(f660,plain,(
% 2.18/0.66    spl4_22 <=> k6_partfun1(sK1) = sK3),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.18/0.66  fof(f1181,plain,(
% 2.18/0.66    spl4_44),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f1180])).
% 2.18/0.66  fof(f1180,plain,(
% 2.18/0.66    $false | spl4_44),
% 2.18/0.66    inference(subsumption_resolution,[],[f1179,f133])).
% 2.18/0.66  fof(f133,plain,(
% 2.18/0.66    v1_relat_1(sK3)),
% 2.18/0.66    inference(resolution,[],[f86,f62])).
% 2.18/0.66  fof(f86,plain,(
% 2.18/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f29])).
% 2.18/0.66  fof(f29,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.66    inference(ennf_transformation,[],[f11])).
% 2.18/0.66  fof(f11,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.18/0.66  fof(f1179,plain,(
% 2.18/0.66    ~v1_relat_1(sK3) | spl4_44),
% 2.18/0.66    inference(subsumption_resolution,[],[f1178,f235])).
% 2.18/0.66  fof(f235,plain,(
% 2.18/0.66    v5_relat_1(sK3,sK1)),
% 2.18/0.66    inference(resolution,[],[f89,f62])).
% 2.18/0.66  fof(f89,plain,(
% 2.18/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f31])).
% 2.18/0.66  fof(f31,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.66    inference(ennf_transformation,[],[f12])).
% 2.18/0.66  fof(f12,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.18/0.66  fof(f1178,plain,(
% 2.18/0.66    ~v5_relat_1(sK3,sK1) | ~v1_relat_1(sK3) | spl4_44),
% 2.18/0.66    inference(resolution,[],[f1176,f75])).
% 2.18/0.66  fof(f75,plain,(
% 2.18/0.66    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f47])).
% 2.18/0.66  fof(f47,plain,(
% 2.18/0.66    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.18/0.66    inference(nnf_transformation,[],[f26])).
% 2.18/0.66  fof(f26,plain,(
% 2.18/0.66    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.18/0.66    inference(ennf_transformation,[],[f6])).
% 2.18/0.66  fof(f6,axiom,(
% 2.18/0.66    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.18/0.66  fof(f1176,plain,(
% 2.18/0.66    ~r1_tarski(k2_relat_1(sK3),sK1) | spl4_44),
% 2.18/0.66    inference(avatar_component_clause,[],[f1174])).
% 2.18/0.66  fof(f1174,plain,(
% 2.18/0.66    spl4_44 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 2.18/0.66  fof(f1177,plain,(
% 2.18/0.66    spl4_22 | ~spl4_44 | ~spl4_5 | ~spl4_7),
% 2.18/0.66    inference(avatar_split_clause,[],[f1172,f347,f337,f1174,f660])).
% 2.18/0.66  fof(f337,plain,(
% 2.18/0.66    spl4_5 <=> sK1 = k1_relset_1(sK1,sK1,sK2)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.18/0.66  fof(f347,plain,(
% 2.18/0.66    spl4_7 <=> sK1 = k1_relset_1(sK1,sK1,sK3)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.18/0.66  fof(f1172,plain,(
% 2.18/0.66    ~r1_tarski(k2_relat_1(sK3),sK1) | k6_partfun1(sK1) = sK3 | (~spl4_5 | ~spl4_7)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1171,f459])).
% 2.18/0.66  fof(f459,plain,(
% 2.18/0.66    sK1 = k1_relat_1(sK2) | ~spl4_5),
% 2.18/0.66    inference(forward_demodulation,[],[f273,f339])).
% 2.18/0.66  fof(f339,plain,(
% 2.18/0.66    sK1 = k1_relset_1(sK1,sK1,sK2) | ~spl4_5),
% 2.18/0.66    inference(avatar_component_clause,[],[f337])).
% 2.18/0.66  fof(f273,plain,(
% 2.18/0.66    k1_relat_1(sK2) = k1_relset_1(sK1,sK1,sK2)),
% 2.18/0.66    inference(resolution,[],[f87,f59])).
% 2.18/0.66  fof(f59,plain,(
% 2.18/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.18/0.66    inference(cnf_transformation,[],[f46])).
% 2.18/0.66  fof(f87,plain,(
% 2.18/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f30])).
% 2.18/0.66  fof(f30,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.66    inference(ennf_transformation,[],[f13])).
% 2.18/0.66  fof(f13,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.18/0.66  fof(f1171,plain,(
% 2.18/0.66    sK1 != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK3),sK1) | k6_partfun1(sK1) = sK3 | ~spl4_7),
% 2.18/0.66    inference(forward_demodulation,[],[f1170,f492])).
% 2.18/0.66  fof(f492,plain,(
% 2.18/0.66    sK1 = k1_relat_1(sK3) | ~spl4_7),
% 2.18/0.66    inference(forward_demodulation,[],[f274,f349])).
% 2.18/0.66  fof(f349,plain,(
% 2.18/0.66    sK1 = k1_relset_1(sK1,sK1,sK3) | ~spl4_7),
% 2.18/0.66    inference(avatar_component_clause,[],[f347])).
% 2.18/0.66  fof(f274,plain,(
% 2.18/0.66    k1_relat_1(sK3) = k1_relset_1(sK1,sK1,sK3)),
% 2.18/0.66    inference(resolution,[],[f87,f62])).
% 2.18/0.66  fof(f1170,plain,(
% 2.18/0.66    ~r1_tarski(k2_relat_1(sK3),sK1) | k6_partfun1(sK1) = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~spl4_7),
% 2.18/0.66    inference(forward_demodulation,[],[f1169,f492])).
% 2.18/0.66  fof(f1169,plain,(
% 2.18/0.66    k6_partfun1(sK1) = sK3 | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3)) | k1_relat_1(sK2) != k1_relat_1(sK3) | ~spl4_7),
% 2.18/0.66    inference(forward_demodulation,[],[f1168,f492])).
% 2.18/0.66  fof(f1168,plain,(
% 2.18/0.66    sK3 = k6_partfun1(k1_relat_1(sK3)) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3)) | k1_relat_1(sK2) != k1_relat_1(sK3)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1167,f132])).
% 2.18/0.66  fof(f132,plain,(
% 2.18/0.66    v1_relat_1(sK2)),
% 2.18/0.66    inference(resolution,[],[f86,f59])).
% 2.18/0.66  fof(f1167,plain,(
% 2.18/0.66    sK3 = k6_partfun1(k1_relat_1(sK3)) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3)) | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1166,f57])).
% 2.18/0.66  fof(f57,plain,(
% 2.18/0.66    v1_funct_1(sK2)),
% 2.18/0.66    inference(cnf_transformation,[],[f46])).
% 2.18/0.66  fof(f1166,plain,(
% 2.18/0.66    sK3 = k6_partfun1(k1_relat_1(sK3)) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3)) | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1165,f133])).
% 2.18/0.66  fof(f1165,plain,(
% 2.18/0.66    sK3 = k6_partfun1(k1_relat_1(sK3)) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3)) | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1164,f60])).
% 2.18/0.66  fof(f60,plain,(
% 2.18/0.66    v1_funct_1(sK3)),
% 2.18/0.66    inference(cnf_transformation,[],[f46])).
% 2.18/0.66  fof(f1164,plain,(
% 2.18/0.66    sK3 = k6_partfun1(k1_relat_1(sK3)) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3)) | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1163,f64])).
% 2.18/0.66  fof(f64,plain,(
% 2.18/0.66    v2_funct_1(sK2)),
% 2.18/0.66    inference(cnf_transformation,[],[f46])).
% 2.18/0.66  fof(f1163,plain,(
% 2.18/0.66    sK3 = k6_partfun1(k1_relat_1(sK3)) | ~v2_funct_1(sK2) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3)) | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.18/0.66    inference(trivial_inequality_removal,[],[f1162])).
% 2.18/0.66  fof(f1162,plain,(
% 2.18/0.66    sK2 != sK2 | sK3 = k6_partfun1(k1_relat_1(sK3)) | ~v2_funct_1(sK2) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK3)) | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.18/0.66    inference(superposition,[],[f109,f1131])).
% 2.18/0.66  fof(f1131,plain,(
% 2.18/0.66    sK2 = k5_relat_1(sK3,sK2)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1108,f1078])).
% 2.18/0.66  fof(f1078,plain,(
% 2.18/0.66    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),sK2)),
% 2.18/0.66    inference(backward_demodulation,[],[f63,f869])).
% 2.18/0.66  fof(f869,plain,(
% 2.18/0.66    k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)),
% 2.18/0.66    inference(subsumption_resolution,[],[f864,f60])).
% 2.18/0.66  fof(f864,plain,(
% 2.18/0.66    k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) | ~v1_funct_1(sK3)),
% 2.18/0.66    inference(resolution,[],[f490,f62])).
% 2.18/0.66  fof(f490,plain,(
% 2.18/0.66    ( ! [X17,X15,X16] : (~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) | k1_partfun1(X15,X16,sK1,sK1,X17,sK2) = k5_relat_1(X17,sK2) | ~v1_funct_1(X17)) )),
% 2.18/0.66    inference(subsumption_resolution,[],[f478,f57])).
% 2.18/0.66  fof(f478,plain,(
% 2.18/0.66    ( ! [X17,X15,X16] : (k1_partfun1(X15,X16,sK1,sK1,X17,sK2) = k5_relat_1(X17,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) | ~v1_funct_1(X17)) )),
% 2.18/0.66    inference(resolution,[],[f100,f59])).
% 2.18/0.66  fof(f100,plain,(
% 2.18/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f39])).
% 2.18/0.66  fof(f39,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.18/0.66    inference(flattening,[],[f38])).
% 2.18/0.66  fof(f38,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.18/0.66    inference(ennf_transformation,[],[f18])).
% 2.18/0.66  fof(f18,axiom,(
% 2.18/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.18/0.66  fof(f63,plain,(
% 2.18/0.66    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2),sK2)),
% 2.18/0.66    inference(cnf_transformation,[],[f46])).
% 2.18/0.66  fof(f1108,plain,(
% 2.18/0.66    sK2 = k5_relat_1(sK3,sK2) | ~r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),sK2)),
% 2.18/0.66    inference(resolution,[],[f1084,f443])).
% 2.18/0.66  fof(f443,plain,(
% 2.18/0.66    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | sK2 = X9 | ~r2_relset_1(sK1,sK1,X9,sK2)) )),
% 2.18/0.66    inference(resolution,[],[f98,f59])).
% 2.18/0.66  fof(f98,plain,(
% 2.18/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f56])).
% 2.18/0.66  fof(f1084,plain,(
% 2.18/0.66    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.18/0.66    inference(subsumption_resolution,[],[f1083,f60])).
% 2.18/0.66  fof(f1083,plain,(
% 2.18/0.66    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK3)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1082,f62])).
% 2.18/0.66  fof(f1082,plain,(
% 2.18/0.66    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK3)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1081,f57])).
% 2.18/0.66  fof(f1081,plain,(
% 2.18/0.66    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK3)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1079,f59])).
% 2.18/0.66  fof(f1079,plain,(
% 2.18/0.66    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK3)),
% 2.18/0.66    inference(superposition,[],[f102,f869])).
% 2.18/0.66  fof(f102,plain,(
% 2.18/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f41])).
% 2.18/0.66  fof(f41,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.18/0.66    inference(flattening,[],[f40])).
% 2.18/0.66  fof(f40,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.18/0.66    inference(ennf_transformation,[],[f17])).
% 2.18/0.66  fof(f17,axiom,(
% 2.18/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.18/0.67  fof(f109,plain,(
% 2.18/0.67    ( ! [X2,X1] : (k5_relat_1(X2,X1) != X1 | k6_partfun1(k1_relat_1(X2)) = X2 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X2)) | k1_relat_1(X1) != k1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.18/0.67    inference(equality_resolution,[],[f108])).
% 2.18/0.67  fof(f108,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (k6_partfun1(X0) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f77,f67])).
% 2.18/0.67  fof(f77,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (k6_relat_1(X0) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f28])).
% 2.18/0.67  fof(f28,plain,(
% 2.18/0.67    ! [X0,X1] : (! [X2] : (k6_relat_1(X0) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.18/0.67    inference(flattening,[],[f27])).
% 2.18/0.67  fof(f27,plain,(
% 2.18/0.67    ! [X0,X1] : (! [X2] : ((k6_relat_1(X0) = X2 | (k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.18/0.67    inference(ennf_transformation,[],[f10])).
% 2.18/0.67  fof(f10,axiom,(
% 2.18/0.67    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).
% 2.18/0.67  fof(f400,plain,(
% 2.18/0.67    spl4_7 | spl4_6),
% 2.18/0.67    inference(avatar_split_clause,[],[f399,f341,f347])).
% 2.18/0.67  fof(f399,plain,(
% 2.18/0.67    k1_xboole_0 = sK1 | sK1 = k1_relset_1(sK1,sK1,sK3)),
% 2.18/0.67    inference(subsumption_resolution,[],[f398,f61])).
% 2.18/0.67  fof(f61,plain,(
% 2.18/0.67    v1_funct_2(sK3,sK1,sK1)),
% 2.18/0.67    inference(cnf_transformation,[],[f46])).
% 2.18/0.67  fof(f398,plain,(
% 2.18/0.67    ~v1_funct_2(sK3,sK1,sK1) | k1_xboole_0 = sK1 | sK1 = k1_relset_1(sK1,sK1,sK3)),
% 2.18/0.67    inference(resolution,[],[f243,f90])).
% 2.18/0.67  fof(f90,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 2.18/0.67    inference(cnf_transformation,[],[f54])).
% 2.18/0.67  fof(f54,plain,(
% 2.18/0.67    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 2.18/0.67    inference(rectify,[],[f53])).
% 2.18/0.67  fof(f53,plain,(
% 2.18/0.67    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 2.18/0.67    inference(nnf_transformation,[],[f42])).
% 2.18/0.67  fof(f42,plain,(
% 2.18/0.67    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 2.18/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.18/0.67  fof(f243,plain,(
% 2.18/0.67    sP0(sK1,sK3,sK1)),
% 2.18/0.67    inference(resolution,[],[f94,f62])).
% 2.18/0.67  fof(f94,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f55])).
% 2.18/0.67  fof(f55,plain,(
% 2.18/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.67    inference(nnf_transformation,[],[f43])).
% 2.18/0.67  fof(f43,plain,(
% 2.18/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.67    inference(definition_folding,[],[f33,f42])).
% 2.18/0.67  fof(f33,plain,(
% 2.18/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.67    inference(flattening,[],[f32])).
% 2.18/0.67  fof(f32,plain,(
% 2.18/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.67    inference(ennf_transformation,[],[f16])).
% 2.18/0.67  fof(f16,axiom,(
% 2.18/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.18/0.67  fof(f397,plain,(
% 2.18/0.67    spl4_5 | spl4_6),
% 2.18/0.67    inference(avatar_split_clause,[],[f396,f341,f337])).
% 2.18/0.67  fof(f396,plain,(
% 2.18/0.67    k1_xboole_0 = sK1 | sK1 = k1_relset_1(sK1,sK1,sK2)),
% 2.18/0.67    inference(subsumption_resolution,[],[f395,f58])).
% 2.18/0.67  fof(f58,plain,(
% 2.18/0.67    v1_funct_2(sK2,sK1,sK1)),
% 2.18/0.67    inference(cnf_transformation,[],[f46])).
% 2.18/0.67  fof(f395,plain,(
% 2.18/0.67    ~v1_funct_2(sK2,sK1,sK1) | k1_xboole_0 = sK1 | sK1 = k1_relset_1(sK1,sK1,sK2)),
% 2.18/0.67    inference(resolution,[],[f242,f90])).
% 2.18/0.67  fof(f242,plain,(
% 2.18/0.67    sP0(sK1,sK2,sK1)),
% 2.18/0.67    inference(resolution,[],[f94,f59])).
% 2.18/0.67  % SZS output end Proof for theBenchmark
% 2.18/0.67  % (15901)------------------------------
% 2.18/0.67  % (15901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.67  % (15901)Termination reason: Refutation
% 2.18/0.67  
% 2.18/0.67  % (15901)Memory used [KB]: 11641
% 2.18/0.67  % (15901)Time elapsed: 0.227 s
% 2.18/0.67  % (15901)------------------------------
% 2.18/0.67  % (15901)------------------------------
% 2.18/0.67  % (15894)Success in time 0.308 s
%------------------------------------------------------------------------------
