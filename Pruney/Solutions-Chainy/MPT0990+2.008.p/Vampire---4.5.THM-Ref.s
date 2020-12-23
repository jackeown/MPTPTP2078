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
% DateTime   : Thu Dec  3 13:02:29 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 931 expanded)
%              Number of leaves         :   27 ( 287 expanded)
%              Depth                    :   25
%              Number of atoms          :  540 (8348 expanded)
%              Number of equality atoms :  156 (2824 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f237,f1096,f1150,f2289])).

fof(f2289,plain,
    ( ~ spl4_7
    | ~ spl4_69 ),
    inference(avatar_contradiction_clause,[],[f2288])).

fof(f2288,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f2280,f68])).

fof(f68,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f51,f50])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f2280,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl4_7
    | ~ spl4_69 ),
    inference(backward_demodulation,[],[f1180,f2279])).

fof(f2279,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_7
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f2278,f1668])).

fof(f1668,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_69 ),
    inference(backward_demodulation,[],[f184,f1666])).

fof(f1666,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f1665,f1179])).

fof(f1179,plain,
    ( sK1 = k9_relat_1(sK2,sK0)
    | ~ spl4_69 ),
    inference(backward_demodulation,[],[f355,f1095])).

fof(f1095,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f1093])).

fof(f1093,plain,
    ( spl4_69
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f355,plain,(
    sK1 = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f352,f269])).

fof(f269,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(backward_demodulation,[],[f115,f267])).

fof(f267,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f264,f63])).

fof(f63,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f264,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f92,f59])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f115,plain,(
    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(resolution,[],[f73,f111])).

fof(f111,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f91,f59])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f352,plain,(
    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f317,f107])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f317,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f316,f111])).

fof(f316,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f305,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f305,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f87,f267])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1665,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f1664,f1083])).

fof(f1083,plain,(
    sK0 = k10_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f1077,f102])).

fof(f102,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f69])).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1077,plain,(
    k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f480,f1072])).

fof(f1072,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f1061,f1071])).

fof(f1071,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f1055,f340])).

fof(f340,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f95,f100])).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f70,f69])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
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
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1055,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f64,f895])).

fof(f895,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f891,f57])).

fof(f891,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f360,f59])).

fof(f360,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f357,f60])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f357,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f97,f62])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f64,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f1061,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1060,f57])).

fof(f1060,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1059,f59])).

fof(f1059,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1058,f60])).

fof(f1058,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1056,f62])).

fof(f1056,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f99,f895])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f480,plain,(
    k1_relat_1(k5_relat_1(sK2,sK3)) = k10_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f251,f111])).

fof(f251,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k1_relat_1(k5_relat_1(X6,sK3)) = k10_relat_1(X6,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f77,f112])).

fof(f112,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f91,f62])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f1664,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f1645,f112])).

fof(f1645,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3)))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f1054,f166])).

fof(f166,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f93,f62])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1054,plain,(
    ! [X3] :
      ( ~ v4_relat_1(X3,sK1)
      | k1_relat_1(X3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X3)))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f1053,f111])).

fof(f1053,plain,(
    ! [X3] :
      ( ~ v4_relat_1(X3,sK1)
      | ~ v1_relat_1(sK2)
      | k1_relat_1(X3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X3)))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f1043,f57])).

fof(f1043,plain,(
    ! [X3] :
      ( ~ v4_relat_1(X3,sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k1_relat_1(X3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X3)))
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f302,f267])).

fof(f302,plain,(
    ! [X2,X1] :
      ( ~ v4_relat_1(X2,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_relat_1(X2) = k9_relat_1(X1,k10_relat_1(X1,k1_relat_1(X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f87,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f184,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f104,f112])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f75,f69])).

fof(f75,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f2278,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f2273,f286])).

fof(f286,plain,(
    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f285,f267])).

fof(f285,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f284,f111])).

fof(f284,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f283,f57])).

fof(f283,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f105,f65])).

fof(f65,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f84,f69])).

fof(f84,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f2273,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f1825,f215])).

fof(f215,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl4_7
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1825,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k5_relat_1(k5_relat_1(X15,sK2),sK3) = k5_relat_1(X15,k6_partfun1(sK0)) ) ),
    inference(forward_demodulation,[],[f1823,f1072])).

fof(f1823,plain,(
    ! [X15] :
      ( k5_relat_1(k5_relat_1(X15,sK2),sK3) = k5_relat_1(X15,k5_relat_1(sK2,sK3))
      | ~ v1_relat_1(X15) ) ),
    inference(resolution,[],[f326,f111])).

fof(f326,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | k5_relat_1(k5_relat_1(X10,X11),sK3) = k5_relat_1(X10,k5_relat_1(X11,sK3))
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f78,f112])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1180,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_7
    | ~ spl4_69 ),
    inference(backward_demodulation,[],[f361,f1095])).

fof(f361,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f239,f245])).

fof(f245,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f244,f111])).

fof(f244,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f243,f57])).

fof(f243,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f82,f65])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f239,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2))))
    | ~ spl4_7 ),
    inference(resolution,[],[f215,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f74,f69])).

fof(f74,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f1150,plain,(
    spl4_68 ),
    inference(avatar_contradiction_clause,[],[f1149])).

fof(f1149,plain,
    ( $false
    | spl4_68 ),
    inference(subsumption_resolution,[],[f1148,f111])).

fof(f1148,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_68 ),
    inference(subsumption_resolution,[],[f1147,f165])).

fof(f165,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f93,f59])).

fof(f1147,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl4_68 ),
    inference(resolution,[],[f1091,f85])).

fof(f1091,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_68 ),
    inference(avatar_component_clause,[],[f1089])).

fof(f1089,plain,
    ( spl4_68
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f1096,plain,
    ( ~ spl4_68
    | spl4_69 ),
    inference(avatar_split_clause,[],[f1087,f1093,f1089])).

fof(f1087,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(forward_demodulation,[],[f1086,f102])).

fof(f1086,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f1085,f102])).

fof(f1085,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1084,f112])).

fof(f1084,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1078,f111])).

fof(f1078,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f188,f1072])).

fof(f188,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f76,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f237,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f235,f111])).

fof(f235,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f234,f57])).

fof(f234,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(resolution,[],[f216,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f216,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:43:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (10768)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.50  % (10757)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.50  % (10777)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (10760)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (10758)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (10785)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (10783)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (10765)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.53  % (10766)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.53  % (10782)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.53  % (10767)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.53  % (10756)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.54  % (10762)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.54  % (10764)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.30/0.54  % (10780)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.30/0.54  % (10772)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.30/0.54  % (10781)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.54  % (10786)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.54  % (10761)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.46/0.55  % (10773)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.55  % (10771)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.46/0.55  % (10784)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.46/0.55  % (10763)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.46/0.55  % (10779)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.46/0.55  % (10759)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.46/0.55  % (10774)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.55  % (10769)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.56  % (10775)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.46/0.56  % (10776)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.56  % (10773)Refutation not found, incomplete strategy% (10773)------------------------------
% 1.46/0.56  % (10773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (10773)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (10773)Memory used [KB]: 10746
% 1.46/0.56  % (10773)Time elapsed: 0.147 s
% 1.46/0.56  % (10773)------------------------------
% 1.46/0.56  % (10773)------------------------------
% 1.46/0.56  % (10778)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.02/0.66  % (10762)Refutation found. Thanks to Tanya!
% 2.02/0.66  % SZS status Theorem for theBenchmark
% 2.42/0.68  % SZS output start Proof for theBenchmark
% 2.42/0.68  fof(f2307,plain,(
% 2.42/0.68    $false),
% 2.42/0.68    inference(avatar_sat_refutation,[],[f237,f1096,f1150,f2289])).
% 2.42/0.68  fof(f2289,plain,(
% 2.42/0.68    ~spl4_7 | ~spl4_69),
% 2.42/0.68    inference(avatar_contradiction_clause,[],[f2288])).
% 2.42/0.68  fof(f2288,plain,(
% 2.42/0.68    $false | (~spl4_7 | ~spl4_69)),
% 2.42/0.68    inference(subsumption_resolution,[],[f2280,f68])).
% 2.42/0.68  fof(f68,plain,(
% 2.42/0.68    k2_funct_1(sK2) != sK3),
% 2.42/0.68    inference(cnf_transformation,[],[f52])).
% 2.42/0.68  fof(f52,plain,(
% 2.42/0.68    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.42/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f51,f50])).
% 2.42/0.68  fof(f50,plain,(
% 2.42/0.68    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.42/0.68    introduced(choice_axiom,[])).
% 2.42/0.68  fof(f51,plain,(
% 2.42/0.68    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.42/0.68    introduced(choice_axiom,[])).
% 2.42/0.68  fof(f25,plain,(
% 2.42/0.68    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.42/0.68    inference(flattening,[],[f24])).
% 2.42/0.68  fof(f24,plain,(
% 2.42/0.68    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.42/0.68    inference(ennf_transformation,[],[f23])).
% 2.42/0.68  fof(f23,negated_conjecture,(
% 2.42/0.68    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.42/0.68    inference(negated_conjecture,[],[f22])).
% 2.42/0.68  fof(f22,conjecture,(
% 2.42/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.42/0.68  fof(f2280,plain,(
% 2.42/0.68    k2_funct_1(sK2) = sK3 | (~spl4_7 | ~spl4_69)),
% 2.42/0.68    inference(backward_demodulation,[],[f1180,f2279])).
% 2.42/0.68  fof(f2279,plain,(
% 2.42/0.68    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl4_7 | ~spl4_69)),
% 2.42/0.68    inference(forward_demodulation,[],[f2278,f1668])).
% 2.42/0.68  fof(f1668,plain,(
% 2.42/0.68    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_69),
% 2.42/0.68    inference(backward_demodulation,[],[f184,f1666])).
% 2.42/0.68  fof(f1666,plain,(
% 2.42/0.68    sK1 = k1_relat_1(sK3) | ~spl4_69),
% 2.42/0.68    inference(forward_demodulation,[],[f1665,f1179])).
% 2.42/0.68  fof(f1179,plain,(
% 2.42/0.68    sK1 = k9_relat_1(sK2,sK0) | ~spl4_69),
% 2.42/0.68    inference(backward_demodulation,[],[f355,f1095])).
% 2.42/0.68  fof(f1095,plain,(
% 2.42/0.68    sK0 = k1_relat_1(sK2) | ~spl4_69),
% 2.42/0.68    inference(avatar_component_clause,[],[f1093])).
% 2.42/0.68  fof(f1093,plain,(
% 2.42/0.68    spl4_69 <=> sK0 = k1_relat_1(sK2)),
% 2.42/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 2.42/0.68  fof(f355,plain,(
% 2.42/0.68    sK1 = k9_relat_1(sK2,k1_relat_1(sK2))),
% 2.42/0.68    inference(forward_demodulation,[],[f352,f269])).
% 2.42/0.68  fof(f269,plain,(
% 2.42/0.68    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 2.42/0.68    inference(backward_demodulation,[],[f115,f267])).
% 2.42/0.68  fof(f267,plain,(
% 2.42/0.68    sK1 = k2_relat_1(sK2)),
% 2.42/0.68    inference(forward_demodulation,[],[f264,f63])).
% 2.42/0.68  fof(f63,plain,(
% 2.42/0.68    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.42/0.68    inference(cnf_transformation,[],[f52])).
% 2.42/0.68  fof(f264,plain,(
% 2.42/0.68    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.42/0.68    inference(resolution,[],[f92,f59])).
% 2.42/0.68  fof(f59,plain,(
% 2.42/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.42/0.68    inference(cnf_transformation,[],[f52])).
% 2.42/0.68  fof(f92,plain,(
% 2.42/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f42])).
% 2.42/0.68  fof(f42,plain,(
% 2.42/0.68    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.42/0.68    inference(ennf_transformation,[],[f16])).
% 2.42/0.68  fof(f16,axiom,(
% 2.42/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.42/0.68  fof(f115,plain,(
% 2.42/0.68    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)),
% 2.42/0.68    inference(resolution,[],[f73,f111])).
% 2.42/0.68  fof(f111,plain,(
% 2.42/0.68    v1_relat_1(sK2)),
% 2.42/0.68    inference(resolution,[],[f91,f59])).
% 2.42/0.68  fof(f91,plain,(
% 2.42/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f41])).
% 2.42/0.68  fof(f41,plain,(
% 2.42/0.68    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.42/0.68    inference(ennf_transformation,[],[f14])).
% 2.42/0.68  fof(f14,axiom,(
% 2.42/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.42/0.68  fof(f73,plain,(
% 2.42/0.68    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f26])).
% 2.42/0.68  fof(f26,plain,(
% 2.42/0.68    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.42/0.68    inference(ennf_transformation,[],[f3])).
% 2.42/0.68  fof(f3,axiom,(
% 2.42/0.68    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.42/0.68  fof(f352,plain,(
% 2.42/0.68    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 2.42/0.68    inference(resolution,[],[f317,f107])).
% 2.42/0.68  fof(f107,plain,(
% 2.42/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.42/0.68    inference(equality_resolution,[],[f89])).
% 2.42/0.68  fof(f89,plain,(
% 2.42/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.42/0.68    inference(cnf_transformation,[],[f55])).
% 2.42/0.68  fof(f55,plain,(
% 2.42/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.42/0.68    inference(flattening,[],[f54])).
% 2.42/0.68  fof(f54,plain,(
% 2.42/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.42/0.68    inference(nnf_transformation,[],[f1])).
% 2.42/0.68  fof(f1,axiom,(
% 2.42/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.42/0.68  fof(f317,plain,(
% 2.42/0.68    ( ! [X3] : (~r1_tarski(X3,sK1) | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3) )),
% 2.42/0.68    inference(subsumption_resolution,[],[f316,f111])).
% 2.42/0.68  fof(f316,plain,(
% 2.42/0.68    ( ! [X3] : (~r1_tarski(X3,sK1) | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3 | ~v1_relat_1(sK2)) )),
% 2.42/0.68    inference(subsumption_resolution,[],[f305,f57])).
% 2.42/0.68  fof(f57,plain,(
% 2.42/0.68    v1_funct_1(sK2)),
% 2.42/0.68    inference(cnf_transformation,[],[f52])).
% 2.42/0.68  fof(f305,plain,(
% 2.42/0.68    ( ! [X3] : (~r1_tarski(X3,sK1) | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 2.42/0.68    inference(superposition,[],[f87,f267])).
% 2.42/0.68  fof(f87,plain,(
% 2.42/0.68    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f40])).
% 2.42/0.68  fof(f40,plain,(
% 2.42/0.68    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.42/0.68    inference(flattening,[],[f39])).
% 2.42/0.68  fof(f39,plain,(
% 2.42/0.68    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.42/0.68    inference(ennf_transformation,[],[f11])).
% 2.42/0.68  fof(f11,axiom,(
% 2.42/0.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 2.42/0.68  fof(f1665,plain,(
% 2.42/0.68    k1_relat_1(sK3) = k9_relat_1(sK2,sK0)),
% 2.42/0.68    inference(forward_demodulation,[],[f1664,f1083])).
% 2.42/0.68  fof(f1083,plain,(
% 2.42/0.68    sK0 = k10_relat_1(sK2,k1_relat_1(sK3))),
% 2.42/0.68    inference(forward_demodulation,[],[f1077,f102])).
% 2.42/0.68  fof(f102,plain,(
% 2.42/0.68    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.42/0.68    inference(definition_unfolding,[],[f71,f69])).
% 2.42/0.68  fof(f69,plain,(
% 2.42/0.68    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f21])).
% 2.42/0.68  fof(f21,axiom,(
% 2.42/0.68    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.42/0.68  fof(f71,plain,(
% 2.42/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.42/0.68    inference(cnf_transformation,[],[f7])).
% 2.42/0.68  fof(f7,axiom,(
% 2.42/0.68    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.42/0.68  fof(f1077,plain,(
% 2.42/0.68    k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0))),
% 2.42/0.68    inference(backward_demodulation,[],[f480,f1072])).
% 2.42/0.68  fof(f1072,plain,(
% 2.42/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.42/0.68    inference(global_subsumption,[],[f1061,f1071])).
% 2.42/0.68  fof(f1071,plain,(
% 2.42/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.42/0.68    inference(resolution,[],[f1055,f340])).
% 2.42/0.68  fof(f340,plain,(
% 2.42/0.68    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.42/0.68    inference(resolution,[],[f95,f100])).
% 2.42/0.68  fof(f100,plain,(
% 2.42/0.68    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.42/0.68    inference(definition_unfolding,[],[f70,f69])).
% 2.42/0.68  fof(f70,plain,(
% 2.42/0.68    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.42/0.68    inference(cnf_transformation,[],[f18])).
% 2.42/0.68  fof(f18,axiom,(
% 2.42/0.68    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.42/0.68  fof(f95,plain,(
% 2.42/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.42/0.68    inference(cnf_transformation,[],[f56])).
% 2.42/0.68  fof(f56,plain,(
% 2.42/0.68    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.42/0.68    inference(nnf_transformation,[],[f45])).
% 2.42/0.68  fof(f45,plain,(
% 2.42/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.42/0.68    inference(flattening,[],[f44])).
% 2.42/0.68  fof(f44,plain,(
% 2.42/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.42/0.68    inference(ennf_transformation,[],[f17])).
% 2.42/0.68  fof(f17,axiom,(
% 2.42/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.42/0.68  fof(f1055,plain,(
% 2.42/0.68    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.42/0.68    inference(backward_demodulation,[],[f64,f895])).
% 2.42/0.68  fof(f895,plain,(
% 2.42/0.68    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.42/0.68    inference(subsumption_resolution,[],[f891,f57])).
% 2.42/0.68  fof(f891,plain,(
% 2.42/0.68    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 2.42/0.68    inference(resolution,[],[f360,f59])).
% 2.42/0.68  fof(f360,plain,(
% 2.42/0.68    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 2.42/0.68    inference(subsumption_resolution,[],[f357,f60])).
% 2.42/0.68  fof(f60,plain,(
% 2.42/0.68    v1_funct_1(sK3)),
% 2.42/0.68    inference(cnf_transformation,[],[f52])).
% 2.42/0.68  fof(f357,plain,(
% 2.42/0.68    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 2.42/0.68    inference(resolution,[],[f97,f62])).
% 2.42/0.68  fof(f62,plain,(
% 2.42/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.42/0.68    inference(cnf_transformation,[],[f52])).
% 2.42/0.68  fof(f97,plain,(
% 2.42/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f47])).
% 2.42/0.68  fof(f47,plain,(
% 2.42/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.42/0.68    inference(flattening,[],[f46])).
% 2.42/0.68  fof(f46,plain,(
% 2.42/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.42/0.68    inference(ennf_transformation,[],[f20])).
% 2.42/0.68  fof(f20,axiom,(
% 2.42/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.42/0.68  fof(f64,plain,(
% 2.42/0.68    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.42/0.68    inference(cnf_transformation,[],[f52])).
% 2.42/0.68  fof(f1061,plain,(
% 2.42/0.68    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.42/0.68    inference(subsumption_resolution,[],[f1060,f57])).
% 2.42/0.68  fof(f1060,plain,(
% 2.42/0.68    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.42/0.68    inference(subsumption_resolution,[],[f1059,f59])).
% 2.42/0.68  fof(f1059,plain,(
% 2.42/0.68    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.42/0.68    inference(subsumption_resolution,[],[f1058,f60])).
% 2.42/0.68  fof(f1058,plain,(
% 2.42/0.68    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.42/0.68    inference(subsumption_resolution,[],[f1056,f62])).
% 2.42/0.68  fof(f1056,plain,(
% 2.42/0.68    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.42/0.68    inference(superposition,[],[f99,f895])).
% 2.42/0.68  fof(f99,plain,(
% 2.42/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f49])).
% 2.42/0.68  fof(f49,plain,(
% 2.42/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.42/0.68    inference(flattening,[],[f48])).
% 2.42/0.68  fof(f48,plain,(
% 2.42/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.42/0.68    inference(ennf_transformation,[],[f19])).
% 2.42/0.68  fof(f19,axiom,(
% 2.42/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.42/0.68  fof(f480,plain,(
% 2.42/0.68    k1_relat_1(k5_relat_1(sK2,sK3)) = k10_relat_1(sK2,k1_relat_1(sK3))),
% 2.42/0.68    inference(resolution,[],[f251,f111])).
% 2.42/0.68  fof(f251,plain,(
% 2.42/0.68    ( ! [X6] : (~v1_relat_1(X6) | k1_relat_1(k5_relat_1(X6,sK3)) = k10_relat_1(X6,k1_relat_1(sK3))) )),
% 2.42/0.68    inference(resolution,[],[f77,f112])).
% 2.42/0.68  fof(f112,plain,(
% 2.42/0.68    v1_relat_1(sK3)),
% 2.42/0.68    inference(resolution,[],[f91,f62])).
% 2.42/0.68  fof(f77,plain,(
% 2.42/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f30])).
% 2.42/0.68  fof(f30,plain,(
% 2.42/0.68    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.42/0.68    inference(ennf_transformation,[],[f4])).
% 2.42/0.68  fof(f4,axiom,(
% 2.42/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.42/0.68  fof(f1664,plain,(
% 2.42/0.68    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3)))),
% 2.42/0.68    inference(subsumption_resolution,[],[f1645,f112])).
% 2.42/0.68  fof(f1645,plain,(
% 2.42/0.68    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) | ~v1_relat_1(sK3)),
% 2.42/0.68    inference(resolution,[],[f1054,f166])).
% 2.42/0.68  fof(f166,plain,(
% 2.42/0.68    v4_relat_1(sK3,sK1)),
% 2.42/0.68    inference(resolution,[],[f93,f62])).
% 2.42/0.68  fof(f93,plain,(
% 2.42/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f43])).
% 2.42/0.68  fof(f43,plain,(
% 2.42/0.68    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.42/0.68    inference(ennf_transformation,[],[f15])).
% 2.42/0.68  fof(f15,axiom,(
% 2.42/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.42/0.68  fof(f1054,plain,(
% 2.42/0.68    ( ! [X3] : (~v4_relat_1(X3,sK1) | k1_relat_1(X3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X3))) | ~v1_relat_1(X3)) )),
% 2.42/0.68    inference(subsumption_resolution,[],[f1053,f111])).
% 2.42/0.68  fof(f1053,plain,(
% 2.42/0.68    ( ! [X3] : (~v4_relat_1(X3,sK1) | ~v1_relat_1(sK2) | k1_relat_1(X3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X3))) | ~v1_relat_1(X3)) )),
% 2.42/0.68    inference(subsumption_resolution,[],[f1043,f57])).
% 2.42/0.68  fof(f1043,plain,(
% 2.42/0.68    ( ! [X3] : (~v4_relat_1(X3,sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(X3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X3))) | ~v1_relat_1(X3)) )),
% 2.42/0.68    inference(superposition,[],[f302,f267])).
% 2.42/0.68  fof(f302,plain,(
% 2.42/0.68    ( ! [X2,X1] : (~v4_relat_1(X2,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_relat_1(X2) = k9_relat_1(X1,k10_relat_1(X1,k1_relat_1(X2))) | ~v1_relat_1(X2)) )),
% 2.42/0.68    inference(resolution,[],[f87,f85])).
% 2.42/0.68  fof(f85,plain,(
% 2.42/0.68    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f53])).
% 2.42/0.68  fof(f53,plain,(
% 2.42/0.68    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.42/0.68    inference(nnf_transformation,[],[f38])).
% 2.42/0.68  fof(f38,plain,(
% 2.42/0.68    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.42/0.68    inference(ennf_transformation,[],[f2])).
% 2.42/0.68  fof(f2,axiom,(
% 2.42/0.68    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.42/0.68  fof(f184,plain,(
% 2.42/0.68    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 2.42/0.68    inference(resolution,[],[f104,f112])).
% 2.42/0.68  fof(f104,plain,(
% 2.42/0.68    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 2.42/0.68    inference(definition_unfolding,[],[f75,f69])).
% 2.42/0.68  fof(f75,plain,(
% 2.42/0.68    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f28])).
% 2.42/0.68  fof(f28,plain,(
% 2.42/0.68    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.42/0.68    inference(ennf_transformation,[],[f8])).
% 2.42/0.68  fof(f8,axiom,(
% 2.42/0.68    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 2.42/0.68  fof(f2278,plain,(
% 2.42/0.68    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_7),
% 2.42/0.68    inference(forward_demodulation,[],[f2273,f286])).
% 2.42/0.68  fof(f286,plain,(
% 2.42/0.68    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.42/0.68    inference(forward_demodulation,[],[f285,f267])).
% 2.42/0.68  fof(f285,plain,(
% 2.42/0.68    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.42/0.68    inference(subsumption_resolution,[],[f284,f111])).
% 2.42/0.68  fof(f284,plain,(
% 2.42/0.68    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 2.42/0.68    inference(subsumption_resolution,[],[f283,f57])).
% 2.42/0.68  fof(f283,plain,(
% 2.42/0.68    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.42/0.68    inference(resolution,[],[f105,f65])).
% 2.42/0.68  fof(f65,plain,(
% 2.42/0.68    v2_funct_1(sK2)),
% 2.42/0.68    inference(cnf_transformation,[],[f52])).
% 2.42/0.68  fof(f105,plain,(
% 2.42/0.68    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.42/0.68    inference(definition_unfolding,[],[f84,f69])).
% 2.42/0.68  fof(f84,plain,(
% 2.42/0.68    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f37])).
% 2.42/0.68  fof(f37,plain,(
% 2.42/0.68    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.42/0.68    inference(flattening,[],[f36])).
% 2.42/0.68  fof(f36,plain,(
% 2.42/0.68    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f13])).
% 2.42/0.68  fof(f13,axiom,(
% 2.42/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.42/0.68  fof(f2273,plain,(
% 2.42/0.68    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) | ~spl4_7),
% 2.42/0.68    inference(resolution,[],[f1825,f215])).
% 2.42/0.68  fof(f215,plain,(
% 2.42/0.68    v1_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 2.42/0.68    inference(avatar_component_clause,[],[f214])).
% 2.42/0.68  fof(f214,plain,(
% 2.42/0.68    spl4_7 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.42/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.42/0.68  fof(f1825,plain,(
% 2.42/0.68    ( ! [X15] : (~v1_relat_1(X15) | k5_relat_1(k5_relat_1(X15,sK2),sK3) = k5_relat_1(X15,k6_partfun1(sK0))) )),
% 2.42/0.68    inference(forward_demodulation,[],[f1823,f1072])).
% 2.42/0.68  fof(f1823,plain,(
% 2.42/0.68    ( ! [X15] : (k5_relat_1(k5_relat_1(X15,sK2),sK3) = k5_relat_1(X15,k5_relat_1(sK2,sK3)) | ~v1_relat_1(X15)) )),
% 2.42/0.68    inference(resolution,[],[f326,f111])).
% 2.42/0.68  fof(f326,plain,(
% 2.42/0.68    ( ! [X10,X11] : (~v1_relat_1(X11) | k5_relat_1(k5_relat_1(X10,X11),sK3) = k5_relat_1(X10,k5_relat_1(X11,sK3)) | ~v1_relat_1(X10)) )),
% 2.42/0.68    inference(resolution,[],[f78,f112])).
% 2.42/0.68  fof(f78,plain,(
% 2.42/0.68    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f31])).
% 2.42/0.68  fof(f31,plain,(
% 2.42/0.68    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.42/0.68    inference(ennf_transformation,[],[f6])).
% 2.42/0.68  fof(f6,axiom,(
% 2.42/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.42/0.68  fof(f1180,plain,(
% 2.42/0.68    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl4_7 | ~spl4_69)),
% 2.42/0.68    inference(backward_demodulation,[],[f361,f1095])).
% 2.42/0.68  fof(f361,plain,(
% 2.42/0.68    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) | ~spl4_7),
% 2.42/0.68    inference(forward_demodulation,[],[f239,f245])).
% 2.42/0.68  fof(f245,plain,(
% 2.42/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.42/0.68    inference(subsumption_resolution,[],[f244,f111])).
% 2.42/0.68  fof(f244,plain,(
% 2.42/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.42/0.68    inference(subsumption_resolution,[],[f243,f57])).
% 2.42/0.68  fof(f243,plain,(
% 2.42/0.68    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.42/0.68    inference(resolution,[],[f82,f65])).
% 2.42/0.68  fof(f82,plain,(
% 2.42/0.68    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f35])).
% 2.42/0.68  fof(f35,plain,(
% 2.42/0.68    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.42/0.68    inference(flattening,[],[f34])).
% 2.42/0.68  fof(f34,plain,(
% 2.42/0.68    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f12])).
% 2.42/0.68  fof(f12,axiom,(
% 2.42/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.42/0.68  fof(f239,plain,(
% 2.42/0.68    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) | ~spl4_7),
% 2.42/0.68    inference(resolution,[],[f215,f103])).
% 2.42/0.68  fof(f103,plain,(
% 2.42/0.68    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 2.42/0.68    inference(definition_unfolding,[],[f74,f69])).
% 2.42/0.68  fof(f74,plain,(
% 2.42/0.68    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f27])).
% 2.42/0.68  fof(f27,plain,(
% 2.42/0.68    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.42/0.68    inference(ennf_transformation,[],[f9])).
% 2.42/0.68  fof(f9,axiom,(
% 2.42/0.68    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.42/0.68  fof(f1150,plain,(
% 2.42/0.68    spl4_68),
% 2.42/0.68    inference(avatar_contradiction_clause,[],[f1149])).
% 2.42/0.68  fof(f1149,plain,(
% 2.42/0.68    $false | spl4_68),
% 2.42/0.68    inference(subsumption_resolution,[],[f1148,f111])).
% 2.42/0.68  fof(f1148,plain,(
% 2.42/0.68    ~v1_relat_1(sK2) | spl4_68),
% 2.42/0.68    inference(subsumption_resolution,[],[f1147,f165])).
% 2.42/0.68  fof(f165,plain,(
% 2.42/0.68    v4_relat_1(sK2,sK0)),
% 2.42/0.68    inference(resolution,[],[f93,f59])).
% 2.42/0.68  fof(f1147,plain,(
% 2.42/0.68    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl4_68),
% 2.42/0.68    inference(resolution,[],[f1091,f85])).
% 2.42/0.68  fof(f1091,plain,(
% 2.42/0.68    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_68),
% 2.42/0.68    inference(avatar_component_clause,[],[f1089])).
% 2.42/0.68  fof(f1089,plain,(
% 2.42/0.68    spl4_68 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 2.42/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 2.42/0.68  fof(f1096,plain,(
% 2.42/0.68    ~spl4_68 | spl4_69),
% 2.42/0.68    inference(avatar_split_clause,[],[f1087,f1093,f1089])).
% 2.42/0.68  fof(f1087,plain,(
% 2.42/0.68    sK0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0)),
% 2.42/0.68    inference(forward_demodulation,[],[f1086,f102])).
% 2.42/0.68  fof(f1086,plain,(
% 2.42/0.68    ~r1_tarski(k1_relat_1(sK2),sK0) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))),
% 2.42/0.68    inference(forward_demodulation,[],[f1085,f102])).
% 2.42/0.68  fof(f1085,plain,(
% 2.42/0.68    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))),
% 2.42/0.68    inference(subsumption_resolution,[],[f1084,f112])).
% 2.42/0.68  fof(f1084,plain,(
% 2.42/0.68    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 2.42/0.68    inference(subsumption_resolution,[],[f1078,f111])).
% 2.42/0.68  fof(f1078,plain,(
% 2.42/0.68    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 2.42/0.68    inference(superposition,[],[f188,f1072])).
% 2.42/0.68  fof(f188,plain,(
% 2.42/0.68    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 2.42/0.68    inference(resolution,[],[f76,f90])).
% 2.42/0.68  fof(f90,plain,(
% 2.42/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f55])).
% 2.42/0.68  fof(f76,plain,(
% 2.42/0.68    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f29])).
% 2.42/0.68  fof(f29,plain,(
% 2.42/0.68    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.42/0.68    inference(ennf_transformation,[],[f5])).
% 2.42/0.68  fof(f5,axiom,(
% 2.42/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 2.42/0.68  fof(f237,plain,(
% 2.42/0.68    spl4_7),
% 2.42/0.68    inference(avatar_contradiction_clause,[],[f236])).
% 2.42/0.68  fof(f236,plain,(
% 2.42/0.68    $false | spl4_7),
% 2.42/0.68    inference(subsumption_resolution,[],[f235,f111])).
% 2.42/0.68  fof(f235,plain,(
% 2.42/0.68    ~v1_relat_1(sK2) | spl4_7),
% 2.42/0.68    inference(subsumption_resolution,[],[f234,f57])).
% 2.42/0.68  fof(f234,plain,(
% 2.42/0.68    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_7),
% 2.42/0.68    inference(resolution,[],[f216,f79])).
% 2.42/0.68  fof(f79,plain,(
% 2.42/0.68    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f33])).
% 2.42/0.68  fof(f33,plain,(
% 2.42/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.42/0.68    inference(flattening,[],[f32])).
% 2.42/0.68  fof(f32,plain,(
% 2.42/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f10])).
% 2.42/0.68  fof(f10,axiom,(
% 2.42/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.42/0.68  fof(f216,plain,(
% 2.42/0.68    ~v1_relat_1(k2_funct_1(sK2)) | spl4_7),
% 2.42/0.68    inference(avatar_component_clause,[],[f214])).
% 2.42/0.68  % SZS output end Proof for theBenchmark
% 2.42/0.68  % (10762)------------------------------
% 2.42/0.68  % (10762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.42/0.68  % (10762)Termination reason: Refutation
% 2.42/0.68  
% 2.42/0.68  % (10762)Memory used [KB]: 12409
% 2.42/0.68  % (10762)Time elapsed: 0.252 s
% 2.42/0.68  % (10762)------------------------------
% 2.42/0.68  % (10762)------------------------------
% 2.42/0.68  % (10752)Success in time 0.322 s
%------------------------------------------------------------------------------
