%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:28 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 619 expanded)
%              Number of leaves         :   22 ( 188 expanded)
%              Depth                    :   27
%              Number of atoms          :  466 (5404 expanded)
%              Number of equality atoms :  129 (1809 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1949,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f215,f1948])).

fof(f1948,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1947])).

fof(f1947,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1946,f62])).

fof(f62,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f1946,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1945,f359])).

fof(f359,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(subsumption_resolution,[],[f354,f103])).

fof(f103,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f83,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f354,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(resolution,[],[f226,f158])).

fof(f158,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f85,f56])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f97,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f63])).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1945,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1944,f1189])).

fof(f1189,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f296,f1168])).

fof(f1168,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f1167,f93])).

fof(f93,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f66,f63])).

fof(f66,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1167,plain,(
    k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1166,f362])).

fof(f362,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f360,f102])).

fof(f102,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f83,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f360,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f175,f358])).

fof(f358,plain,(
    sK2 = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(subsumption_resolution,[],[f353,f102])).

fof(f353,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(resolution,[],[f226,f157])).

fof(f157,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f85,f53])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_partfun1(X0),X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f173,f104])).

fof(f104,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f173,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_partfun1(X0),X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f69,f93])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f1166,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f1165,f93])).

fof(f1165,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1164,f103])).

fof(f1164,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1157,f102])).

fof(f1157,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f169,f1130])).

fof(f1130,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f1087,f1129])).

fof(f1129,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f1059,f294])).

fof(f294,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f87,f65])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f1059,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f58,f640])).

fof(f640,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f637,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f637,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f314,f53])).

fof(f314,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f311,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f311,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f89,f56])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f58,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f1087,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1086,f51])).

fof(f1086,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1085,f53])).

fof(f1085,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1084,f54])).

fof(f1084,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1064,f56])).

fof(f1064,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f91,f640])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f169,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f69,f82])).

fof(f82,plain,(
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

fof(f296,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f219,f218])).

fof(f218,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f217,f102])).

fof(f217,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f216,f51])).

fof(f216,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f59])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f219,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2))))
    | ~ spl4_7 ),
    inference(resolution,[],[f193,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f68,f63])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f193,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl4_7
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1944,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1936,f256])).

fof(f256,plain,(
    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f255,f237])).

fof(f237,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f234,f57])).

fof(f57,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f234,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f84,f53])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f255,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f254,f102])).

fof(f254,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f253,f51])).

fof(f253,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f95,f59])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f76,f63])).

fof(f76,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f1936,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f1355,f193])).

fof(f1355,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k5_relat_1(k5_relat_1(X15,sK2),sK3) = k5_relat_1(X15,k6_partfun1(sK0)) ) ),
    inference(forward_demodulation,[],[f1353,f1130])).

fof(f1353,plain,(
    ! [X15] :
      ( k5_relat_1(k5_relat_1(X15,sK2),sK3) = k5_relat_1(X15,k5_relat_1(sK2,sK3))
      | ~ v1_relat_1(X15) ) ),
    inference(resolution,[],[f275,f102])).

fof(f275,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | k5_relat_1(k5_relat_1(X10,X11),sK3) = k5_relat_1(X10,k5_relat_1(X11,sK3))
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f70,f103])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f215,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f213,f102])).

fof(f213,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f212,f51])).

fof(f212,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(resolution,[],[f194,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f194,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 21:09:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.44  % (1905)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.48  % (1930)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.50  % (1925)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.50  % (1917)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.51  % (1922)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.51  % (1908)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (1913)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.52  % (1904)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.52  % (1906)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.52  % (1907)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.52  % (1903)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.53  % (1912)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.53  % (1902)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.53  % (1931)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.53  % (1920)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.53  % (1932)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.53  % (1929)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (1923)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.54  % (1924)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.54  % (1909)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.54  % (1921)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.54  % (1916)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.54  % (1911)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.54  % (1915)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.54  % (1919)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.54  % (1918)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.54  % (1928)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.55  % (1910)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.55  % (1927)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.56  % (1919)Refutation not found, incomplete strategy% (1919)------------------------------
% 0.19/0.56  % (1919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (1919)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (1919)Memory used [KB]: 10746
% 0.19/0.56  % (1919)Time elapsed: 0.175 s
% 0.19/0.56  % (1919)------------------------------
% 0.19/0.56  % (1919)------------------------------
% 1.54/0.58  % (1926)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.80/0.61  % (1908)Refutation found. Thanks to Tanya!
% 1.80/0.61  % SZS status Theorem for theBenchmark
% 1.80/0.61  % SZS output start Proof for theBenchmark
% 1.80/0.61  fof(f1949,plain,(
% 1.80/0.61    $false),
% 1.80/0.61    inference(avatar_sat_refutation,[],[f215,f1948])).
% 1.80/0.61  fof(f1948,plain,(
% 1.80/0.61    ~spl4_7),
% 1.80/0.61    inference(avatar_contradiction_clause,[],[f1947])).
% 1.80/0.61  fof(f1947,plain,(
% 1.80/0.61    $false | ~spl4_7),
% 1.80/0.61    inference(subsumption_resolution,[],[f1946,f62])).
% 1.80/0.61  fof(f62,plain,(
% 1.80/0.61    k2_funct_1(sK2) != sK3),
% 1.80/0.61    inference(cnf_transformation,[],[f46])).
% 1.80/0.61  fof(f46,plain,(
% 1.80/0.61    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.80/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f45,f44])).
% 1.80/0.61  fof(f44,plain,(
% 1.80/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.80/0.61    introduced(choice_axiom,[])).
% 1.80/0.61  fof(f45,plain,(
% 1.80/0.61    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.80/0.61    introduced(choice_axiom,[])).
% 1.80/0.61  fof(f22,plain,(
% 1.80/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.80/0.61    inference(flattening,[],[f21])).
% 1.80/0.61  fof(f21,plain,(
% 1.80/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.80/0.61    inference(ennf_transformation,[],[f20])).
% 1.80/0.61  fof(f20,negated_conjecture,(
% 1.80/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.80/0.61    inference(negated_conjecture,[],[f19])).
% 1.80/0.61  fof(f19,conjecture,(
% 1.80/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.80/0.61  fof(f1946,plain,(
% 1.80/0.61    k2_funct_1(sK2) = sK3 | ~spl4_7),
% 1.80/0.61    inference(forward_demodulation,[],[f1945,f359])).
% 1.80/0.61  fof(f359,plain,(
% 1.80/0.61    sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.80/0.61    inference(subsumption_resolution,[],[f354,f103])).
% 1.80/0.61  fof(f103,plain,(
% 1.80/0.61    v1_relat_1(sK3)),
% 1.80/0.61    inference(resolution,[],[f83,f56])).
% 1.80/0.61  fof(f56,plain,(
% 1.80/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.80/0.61    inference(cnf_transformation,[],[f46])).
% 1.80/0.61  fof(f83,plain,(
% 1.80/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f35])).
% 1.80/0.61  fof(f35,plain,(
% 1.80/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.61    inference(ennf_transformation,[],[f11])).
% 1.80/0.61  fof(f11,axiom,(
% 1.80/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.80/0.61  fof(f354,plain,(
% 1.80/0.61    ~v1_relat_1(sK3) | sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.80/0.61    inference(resolution,[],[f226,f158])).
% 1.80/0.61  fof(f158,plain,(
% 1.80/0.61    v4_relat_1(sK3,sK1)),
% 1.80/0.61    inference(resolution,[],[f85,f56])).
% 1.80/0.61  fof(f85,plain,(
% 1.80/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f37])).
% 1.80/0.61  fof(f37,plain,(
% 1.80/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.61    inference(ennf_transformation,[],[f12])).
% 1.80/0.61  fof(f12,axiom,(
% 1.80/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.80/0.61  fof(f226,plain,(
% 1.80/0.61    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k5_relat_1(k6_partfun1(X0),X1) = X1) )),
% 1.80/0.61    inference(duplicate_literal_removal,[],[f220])).
% 1.80/0.61  fof(f220,plain,(
% 1.80/0.61    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.80/0.61    inference(resolution,[],[f97,f78])).
% 1.80/0.61  fof(f78,plain,(
% 1.80/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f47])).
% 1.80/0.61  fof(f47,plain,(
% 1.80/0.61    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.80/0.61    inference(nnf_transformation,[],[f34])).
% 1.80/0.61  fof(f34,plain,(
% 1.80/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.80/0.61    inference(ennf_transformation,[],[f2])).
% 1.80/0.61  fof(f2,axiom,(
% 1.80/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.80/0.61  fof(f97,plain,(
% 1.80/0.61    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_partfun1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 1.80/0.61    inference(definition_unfolding,[],[f77,f63])).
% 1.80/0.61  fof(f63,plain,(
% 1.80/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f18])).
% 1.80/0.61  fof(f18,axiom,(
% 1.80/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.80/0.61  fof(f77,plain,(
% 1.80/0.61    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f33])).
% 1.80/0.61  fof(f33,plain,(
% 1.80/0.61    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.80/0.61    inference(flattening,[],[f32])).
% 1.80/0.61  fof(f32,plain,(
% 1.80/0.61    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.80/0.61    inference(ennf_transformation,[],[f6])).
% 1.80/0.61  fof(f6,axiom,(
% 1.80/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 1.80/0.61  fof(f1945,plain,(
% 1.80/0.61    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_7),
% 1.80/0.61    inference(forward_demodulation,[],[f1944,f1189])).
% 1.80/0.61  fof(f1189,plain,(
% 1.80/0.61    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_7),
% 1.80/0.61    inference(backward_demodulation,[],[f296,f1168])).
% 1.80/0.61  fof(f1168,plain,(
% 1.80/0.61    sK0 = k1_relat_1(sK2)),
% 1.80/0.61    inference(forward_demodulation,[],[f1167,f93])).
% 1.80/0.61  fof(f93,plain,(
% 1.80/0.61    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.80/0.61    inference(definition_unfolding,[],[f66,f63])).
% 1.80/0.61  fof(f66,plain,(
% 1.80/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.80/0.61    inference(cnf_transformation,[],[f5])).
% 1.80/0.61  fof(f5,axiom,(
% 1.80/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.80/0.61  fof(f1167,plain,(
% 1.80/0.61    k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))),
% 1.80/0.61    inference(subsumption_resolution,[],[f1166,f362])).
% 1.80/0.61  fof(f362,plain,(
% 1.80/0.61    r1_tarski(k1_relat_1(sK2),sK0)),
% 1.80/0.61    inference(subsumption_resolution,[],[f360,f102])).
% 1.80/0.61  fof(f102,plain,(
% 1.80/0.61    v1_relat_1(sK2)),
% 1.80/0.61    inference(resolution,[],[f83,f53])).
% 1.80/0.61  fof(f53,plain,(
% 1.80/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.80/0.61    inference(cnf_transformation,[],[f46])).
% 1.80/0.61  fof(f360,plain,(
% 1.80/0.61    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 1.80/0.61    inference(superposition,[],[f175,f358])).
% 1.80/0.61  fof(f358,plain,(
% 1.80/0.61    sK2 = k5_relat_1(k6_partfun1(sK0),sK2)),
% 1.80/0.61    inference(subsumption_resolution,[],[f353,f102])).
% 1.80/0.61  fof(f353,plain,(
% 1.80/0.61    ~v1_relat_1(sK2) | sK2 = k5_relat_1(k6_partfun1(sK0),sK2)),
% 1.80/0.61    inference(resolution,[],[f226,f157])).
% 1.80/0.61  fof(f157,plain,(
% 1.80/0.61    v4_relat_1(sK2,sK0)),
% 1.80/0.61    inference(resolution,[],[f85,f53])).
% 1.80/0.61  fof(f175,plain,(
% 1.80/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(k6_partfun1(X0),X1)),X0) | ~v1_relat_1(X1)) )),
% 1.80/0.61    inference(subsumption_resolution,[],[f173,f104])).
% 1.80/0.61  fof(f104,plain,(
% 1.80/0.61    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.80/0.61    inference(resolution,[],[f83,f65])).
% 1.80/0.61  fof(f65,plain,(
% 1.80/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.80/0.61    inference(cnf_transformation,[],[f16])).
% 1.80/0.61  fof(f16,axiom,(
% 1.80/0.61    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.80/0.61  fof(f173,plain,(
% 1.80/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(k6_partfun1(X0),X1)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(k6_partfun1(X0))) )),
% 1.80/0.61    inference(superposition,[],[f69,f93])).
% 1.80/0.61  fof(f69,plain,(
% 1.80/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f24])).
% 1.80/0.61  fof(f24,plain,(
% 1.80/0.61    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.80/0.61    inference(ennf_transformation,[],[f3])).
% 1.80/0.61  fof(f3,axiom,(
% 1.80/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 1.80/0.61  fof(f1166,plain,(
% 1.80/0.61    ~r1_tarski(k1_relat_1(sK2),sK0) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))),
% 1.80/0.61    inference(forward_demodulation,[],[f1165,f93])).
% 1.80/0.61  fof(f1165,plain,(
% 1.80/0.61    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))),
% 1.80/0.61    inference(subsumption_resolution,[],[f1164,f103])).
% 1.80/0.61  fof(f1164,plain,(
% 1.80/0.61    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.80/0.61    inference(subsumption_resolution,[],[f1157,f102])).
% 1.80/0.61  fof(f1157,plain,(
% 1.80/0.61    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.80/0.61    inference(superposition,[],[f169,f1130])).
% 1.80/0.61  fof(f1130,plain,(
% 1.80/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.80/0.61    inference(global_subsumption,[],[f1087,f1129])).
% 1.80/0.61  fof(f1129,plain,(
% 1.80/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.80/0.61    inference(resolution,[],[f1059,f294])).
% 1.80/0.61  fof(f294,plain,(
% 1.80/0.61    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.80/0.61    inference(resolution,[],[f87,f65])).
% 1.80/0.61  fof(f87,plain,(
% 1.80/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.80/0.61    inference(cnf_transformation,[],[f50])).
% 1.80/0.61  fof(f50,plain,(
% 1.80/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.61    inference(nnf_transformation,[],[f39])).
% 1.80/0.61  fof(f39,plain,(
% 1.80/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.61    inference(flattening,[],[f38])).
% 1.80/0.61  fof(f38,plain,(
% 1.80/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.80/0.61    inference(ennf_transformation,[],[f14])).
% 1.80/0.61  fof(f14,axiom,(
% 1.80/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.80/0.61  fof(f1059,plain,(
% 1.80/0.61    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.80/0.61    inference(backward_demodulation,[],[f58,f640])).
% 1.80/0.61  fof(f640,plain,(
% 1.80/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.80/0.61    inference(subsumption_resolution,[],[f637,f51])).
% 1.80/0.61  fof(f51,plain,(
% 1.80/0.61    v1_funct_1(sK2)),
% 1.80/0.61    inference(cnf_transformation,[],[f46])).
% 1.80/0.61  fof(f637,plain,(
% 1.80/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.80/0.61    inference(resolution,[],[f314,f53])).
% 1.80/0.61  fof(f314,plain,(
% 1.80/0.61    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 1.80/0.61    inference(subsumption_resolution,[],[f311,f54])).
% 1.80/0.61  fof(f54,plain,(
% 1.80/0.61    v1_funct_1(sK3)),
% 1.80/0.61    inference(cnf_transformation,[],[f46])).
% 1.80/0.61  fof(f311,plain,(
% 1.80/0.61    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.80/0.61    inference(resolution,[],[f89,f56])).
% 1.80/0.61  fof(f89,plain,(
% 1.80/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f41])).
% 1.80/0.61  fof(f41,plain,(
% 1.80/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.80/0.61    inference(flattening,[],[f40])).
% 1.80/0.61  fof(f40,plain,(
% 1.80/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.80/0.61    inference(ennf_transformation,[],[f17])).
% 1.80/0.61  fof(f17,axiom,(
% 1.80/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.80/0.61  fof(f58,plain,(
% 1.80/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.80/0.61    inference(cnf_transformation,[],[f46])).
% 1.80/0.61  fof(f1087,plain,(
% 1.80/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.80/0.61    inference(subsumption_resolution,[],[f1086,f51])).
% 1.80/0.61  fof(f1086,plain,(
% 1.80/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.80/0.61    inference(subsumption_resolution,[],[f1085,f53])).
% 1.80/0.61  fof(f1085,plain,(
% 1.80/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.80/0.61    inference(subsumption_resolution,[],[f1084,f54])).
% 1.80/0.61  fof(f1084,plain,(
% 1.80/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.80/0.61    inference(subsumption_resolution,[],[f1064,f56])).
% 1.80/0.61  fof(f1064,plain,(
% 1.80/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.80/0.61    inference(superposition,[],[f91,f640])).
% 1.80/0.61  fof(f91,plain,(
% 1.80/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f43])).
% 1.80/0.61  fof(f43,plain,(
% 1.80/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.80/0.61    inference(flattening,[],[f42])).
% 1.80/0.61  fof(f42,plain,(
% 1.80/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.80/0.61    inference(ennf_transformation,[],[f15])).
% 1.80/0.61  fof(f15,axiom,(
% 1.80/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.80/0.61  fof(f169,plain,(
% 1.80/0.61    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 1.80/0.61    inference(resolution,[],[f69,f82])).
% 1.80/0.61  fof(f82,plain,(
% 1.80/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f49])).
% 1.80/0.61  fof(f49,plain,(
% 1.80/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.80/0.61    inference(flattening,[],[f48])).
% 1.80/0.61  fof(f48,plain,(
% 1.80/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.80/0.61    inference(nnf_transformation,[],[f1])).
% 1.80/0.61  fof(f1,axiom,(
% 1.80/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.80/0.61  fof(f296,plain,(
% 1.80/0.61    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) | ~spl4_7),
% 1.80/0.61    inference(forward_demodulation,[],[f219,f218])).
% 1.80/0.61  fof(f218,plain,(
% 1.80/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.80/0.61    inference(subsumption_resolution,[],[f217,f102])).
% 1.80/0.61  fof(f217,plain,(
% 1.80/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.80/0.61    inference(subsumption_resolution,[],[f216,f51])).
% 1.80/0.61  fof(f216,plain,(
% 1.80/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.80/0.61    inference(resolution,[],[f74,f59])).
% 1.80/0.61  fof(f59,plain,(
% 1.80/0.61    v2_funct_1(sK2)),
% 1.80/0.61    inference(cnf_transformation,[],[f46])).
% 1.80/0.61  fof(f74,plain,(
% 1.80/0.61    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f29])).
% 1.80/0.61  fof(f29,plain,(
% 1.80/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.80/0.61    inference(flattening,[],[f28])).
% 1.80/0.61  fof(f28,plain,(
% 1.80/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.80/0.61    inference(ennf_transformation,[],[f9])).
% 1.80/0.61  fof(f9,axiom,(
% 1.80/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.80/0.61  fof(f219,plain,(
% 1.80/0.61    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) | ~spl4_7),
% 1.80/0.61    inference(resolution,[],[f193,f94])).
% 1.80/0.61  fof(f94,plain,(
% 1.80/0.61    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 1.80/0.61    inference(definition_unfolding,[],[f68,f63])).
% 1.80/0.61  fof(f68,plain,(
% 1.80/0.61    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f23])).
% 1.80/0.61  fof(f23,plain,(
% 1.80/0.61    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.80/0.61    inference(ennf_transformation,[],[f7])).
% 1.80/0.61  fof(f7,axiom,(
% 1.80/0.61    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.80/0.61  fof(f193,plain,(
% 1.80/0.61    v1_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 1.80/0.61    inference(avatar_component_clause,[],[f192])).
% 1.80/0.61  fof(f192,plain,(
% 1.80/0.61    spl4_7 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.80/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.80/0.61  fof(f1944,plain,(
% 1.80/0.61    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_7),
% 1.80/0.61    inference(forward_demodulation,[],[f1936,f256])).
% 1.80/0.61  fof(f256,plain,(
% 1.80/0.61    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.80/0.61    inference(forward_demodulation,[],[f255,f237])).
% 1.80/0.61  fof(f237,plain,(
% 1.80/0.61    sK1 = k2_relat_1(sK2)),
% 1.80/0.61    inference(forward_demodulation,[],[f234,f57])).
% 1.80/0.61  fof(f57,plain,(
% 1.80/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.80/0.61    inference(cnf_transformation,[],[f46])).
% 1.80/0.61  fof(f234,plain,(
% 1.80/0.61    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.80/0.61    inference(resolution,[],[f84,f53])).
% 1.80/0.61  fof(f84,plain,(
% 1.80/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f36])).
% 1.80/0.61  fof(f36,plain,(
% 1.80/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.61    inference(ennf_transformation,[],[f13])).
% 1.80/0.61  fof(f13,axiom,(
% 1.80/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.80/0.61  fof(f255,plain,(
% 1.80/0.61    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.80/0.61    inference(subsumption_resolution,[],[f254,f102])).
% 1.80/0.61  fof(f254,plain,(
% 1.80/0.61    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 1.80/0.61    inference(subsumption_resolution,[],[f253,f51])).
% 1.80/0.61  fof(f253,plain,(
% 1.80/0.61    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.80/0.61    inference(resolution,[],[f95,f59])).
% 1.80/0.61  fof(f95,plain,(
% 1.80/0.61    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.80/0.61    inference(definition_unfolding,[],[f76,f63])).
% 1.80/0.61  fof(f76,plain,(
% 1.80/0.61    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f31])).
% 1.80/0.61  fof(f31,plain,(
% 1.80/0.61    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.80/0.61    inference(flattening,[],[f30])).
% 1.80/0.61  fof(f30,plain,(
% 1.80/0.61    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.80/0.61    inference(ennf_transformation,[],[f10])).
% 1.80/0.61  fof(f10,axiom,(
% 1.80/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.80/0.61  fof(f1936,plain,(
% 1.80/0.61    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) | ~spl4_7),
% 1.80/0.61    inference(resolution,[],[f1355,f193])).
% 1.80/0.61  fof(f1355,plain,(
% 1.80/0.61    ( ! [X15] : (~v1_relat_1(X15) | k5_relat_1(k5_relat_1(X15,sK2),sK3) = k5_relat_1(X15,k6_partfun1(sK0))) )),
% 1.80/0.61    inference(forward_demodulation,[],[f1353,f1130])).
% 1.80/0.61  fof(f1353,plain,(
% 1.80/0.61    ( ! [X15] : (k5_relat_1(k5_relat_1(X15,sK2),sK3) = k5_relat_1(X15,k5_relat_1(sK2,sK3)) | ~v1_relat_1(X15)) )),
% 1.80/0.61    inference(resolution,[],[f275,f102])).
% 1.80/0.61  fof(f275,plain,(
% 1.80/0.61    ( ! [X10,X11] : (~v1_relat_1(X11) | k5_relat_1(k5_relat_1(X10,X11),sK3) = k5_relat_1(X10,k5_relat_1(X11,sK3)) | ~v1_relat_1(X10)) )),
% 1.80/0.61    inference(resolution,[],[f70,f103])).
% 1.80/0.61  fof(f70,plain,(
% 1.80/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f25])).
% 1.80/0.61  fof(f25,plain,(
% 1.80/0.61    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.80/0.61    inference(ennf_transformation,[],[f4])).
% 1.80/0.61  fof(f4,axiom,(
% 1.80/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.80/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.80/0.62  fof(f215,plain,(
% 1.80/0.62    spl4_7),
% 1.80/0.62    inference(avatar_contradiction_clause,[],[f214])).
% 1.80/0.62  fof(f214,plain,(
% 1.80/0.62    $false | spl4_7),
% 1.80/0.62    inference(subsumption_resolution,[],[f213,f102])).
% 1.80/0.62  fof(f213,plain,(
% 1.80/0.62    ~v1_relat_1(sK2) | spl4_7),
% 1.80/0.62    inference(subsumption_resolution,[],[f212,f51])).
% 1.80/0.62  fof(f212,plain,(
% 1.80/0.62    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_7),
% 1.80/0.62    inference(resolution,[],[f194,f71])).
% 1.80/0.62  fof(f71,plain,(
% 1.80/0.62    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.80/0.62    inference(cnf_transformation,[],[f27])).
% 1.80/0.62  fof(f27,plain,(
% 1.80/0.62    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.80/0.62    inference(flattening,[],[f26])).
% 1.80/0.62  fof(f26,plain,(
% 1.80/0.62    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.80/0.62    inference(ennf_transformation,[],[f8])).
% 1.80/0.62  fof(f8,axiom,(
% 1.80/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.80/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.80/0.62  fof(f194,plain,(
% 1.80/0.62    ~v1_relat_1(k2_funct_1(sK2)) | spl4_7),
% 1.80/0.62    inference(avatar_component_clause,[],[f192])).
% 1.80/0.62  % SZS output end Proof for theBenchmark
% 1.80/0.62  % (1908)------------------------------
% 1.80/0.62  % (1908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.62  % (1908)Termination reason: Refutation
% 1.80/0.62  
% 1.80/0.62  % (1908)Memory used [KB]: 12153
% 1.80/0.62  % (1908)Time elapsed: 0.163 s
% 1.80/0.62  % (1908)------------------------------
% 1.80/0.62  % (1908)------------------------------
% 1.80/0.62  % (1900)Success in time 0.267 s
%------------------------------------------------------------------------------
