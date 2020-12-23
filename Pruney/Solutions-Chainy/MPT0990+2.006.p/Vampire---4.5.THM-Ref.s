%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:29 EST 2020

% Result     : Theorem 2.75s
% Output     : Refutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 686 expanded)
%              Number of leaves         :   24 ( 208 expanded)
%              Depth                    :   29
%              Number of atoms          :  516 (5915 expanded)
%              Number of equality atoms :  132 (1962 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1775,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f248,f1772])).

fof(f1772,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1771])).

fof(f1771,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1770,f66])).

fof(f66,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f49,f48])).

fof(f48,plain,
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

fof(f49,plain,
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f1770,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1769,f187])).

fof(f187,plain,(
    sK3 = k7_relat_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f182,f113])).

fof(f113,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f88,f60])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f182,plain,
    ( sK3 = k7_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f84,f168])).

fof(f168,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f90,f60])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f1769,plain,
    ( k2_funct_1(sK2) = k7_relat_1(sK3,sK1)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1768,f1166])).

fof(f1166,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f495,f1141])).

fof(f1141,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1137,f167])).

fof(f167,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f90,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f1137,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f1136,f370])).

fof(f370,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK2))
        | k1_relat_1(sK2) = X1
        | ~ v4_relat_1(sK2,X1) )
    | ~ spl4_7 ),
    inference(resolution,[],[f357,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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

fof(f357,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(sK2),X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_7 ),
    inference(resolution,[],[f351,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_partfun1(X0),X1)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f115,f101])).

fof(f101,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f69,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v4_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f82,f103])).

fof(f103,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f67])).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f351,plain,
    ( ! [X0] :
        ( v4_relat_1(k6_partfun1(k1_relat_1(sK2)),X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f350,f112])).

fof(f112,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f88,f57])).

fof(f350,plain,
    ( ! [X0] :
        ( v4_relat_1(k6_partfun1(k1_relat_1(sK2)),X0)
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f349,f230])).

fof(f230,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl4_7
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f349,plain,(
    ! [X0] :
      ( v4_relat_1(k6_partfun1(k1_relat_1(sK2)),X0)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ v4_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f93,f320])).

fof(f320,plain,(
    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f319,f112])).

fof(f319,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f317,f55])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f317,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f106,f63])).

fof(f63,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f79,f67])).

fof(f79,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k5_relat_1(X1,X2),X0)
        & v1_relat_1(k5_relat_1(X1,X2)) )
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k5_relat_1(X1,X2),X0)
        & v1_relat_1(k5_relat_1(X1,X2)) )
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v4_relat_1(k5_relat_1(X1,X2),X0)
        & v1_relat_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc26_relat_1)).

fof(f1136,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f1135,f112])).

fof(f1135,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1109,f118])).

fof(f118,plain,(
    ! [X2] :
      ( v4_relat_1(X2,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f83,f108])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1109,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f1049,f116])).

fof(f1049,plain,(
    ! [X1] :
      ( v4_relat_1(k6_partfun1(sK0),X1)
      | ~ v4_relat_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f1048,f112])).

fof(f1048,plain,(
    ! [X1] :
      ( v4_relat_1(k6_partfun1(sK0),X1)
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1047,f113])).

fof(f1047,plain,(
    ! [X1] :
      ( v4_relat_1(k6_partfun1(sK0),X1)
      | ~ v1_relat_1(sK3)
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f93,f1031])).

fof(f1031,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f1014,f1030])).

fof(f1030,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f998,f347])).

fof(f347,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f94,f99])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f68,f67])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f998,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f62,f699])).

fof(f699,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f695,f55])).

fof(f695,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f386,f57])).

fof(f386,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f383,f58])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f383,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f96,f60])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f62,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f1014,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1013,f55])).

fof(f1013,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1012,f57])).

fof(f1012,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1011,f58])).

fof(f1011,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1001,f60])).

fof(f1001,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f98,f699])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f495,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f251,f256])).

fof(f256,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f255,f112])).

fof(f255,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f253,f55])).

fof(f253,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f63])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f251,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2))))
    | ~ spl4_7 ),
    inference(resolution,[],[f230,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f73,f67])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f1768,plain,
    ( k7_relat_1(sK3,sK1) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1767,f191])).

fof(f191,plain,(
    ! [X5] : k7_relat_1(sK3,X5) = k5_relat_1(k6_partfun1(X5),sK3) ),
    inference(resolution,[],[f107,f113])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f81,f67])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f1767,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1761,f308])).

fof(f308,plain,(
    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f307,f288])).

fof(f288,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f285,f61])).

fof(f61,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f285,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f89,f57])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f307,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f306,f112])).

fof(f306,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f304,f55])).

fof(f304,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f105,f63])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f80,f67])).

fof(f80,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1761,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f1556,f230])).

fof(f1556,plain,(
    ! [X73] :
      ( ~ v1_relat_1(X73)
      | k5_relat_1(k5_relat_1(X73,sK2),sK3) = k5_relat_1(X73,k6_partfun1(sK0)) ) ),
    inference(forward_demodulation,[],[f1553,f1031])).

fof(f1553,plain,(
    ! [X73] :
      ( k5_relat_1(k5_relat_1(X73,sK2),sK3) = k5_relat_1(X73,k5_relat_1(sK2,sK3))
      | ~ v1_relat_1(X73) ) ),
    inference(resolution,[],[f338,f112])).

fof(f338,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k5_relat_1(k5_relat_1(X19,X20),sK3) = k5_relat_1(X19,k5_relat_1(X20,sK3))
      | ~ v1_relat_1(X19) ) ),
    inference(resolution,[],[f74,f113])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f248,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f246,f112])).

fof(f246,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f245,f55])).

fof(f245,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(resolution,[],[f231,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f231,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:41:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (3300)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (3316)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (3298)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.55  % (3308)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.56  % (3294)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.34/0.57  % (3314)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.57  % (3315)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.57  % (3297)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.57  % (3307)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.57  % (3320)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.63/0.57  % (3293)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.63/0.58  % (3296)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.63/0.58  % (3310)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.63/0.58  % (3312)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.63/0.58  % (3301)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.63/0.58  % (3299)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.58  % (3318)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.63/0.58  % (3322)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.63/0.58  % (3304)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.63/0.59  % (3302)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.63/0.60  % (3306)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.63/0.60  % (3313)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.63/0.60  % (3321)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.63/0.60  % (3292)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.63/0.61  % (3319)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.63/0.62  % (3311)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.63/0.62  % (3305)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.63/0.62  % (3303)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.63/0.64  % (3317)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.63/0.65  % (3309)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.63/0.65  % (3309)Refutation not found, incomplete strategy% (3309)------------------------------
% 1.63/0.65  % (3309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.65  % (3309)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.65  
% 1.63/0.65  % (3309)Memory used [KB]: 10746
% 1.63/0.65  % (3309)Time elapsed: 0.209 s
% 1.63/0.65  % (3309)------------------------------
% 1.63/0.65  % (3309)------------------------------
% 2.75/0.73  % (3299)Refutation found. Thanks to Tanya!
% 2.75/0.73  % SZS status Theorem for theBenchmark
% 2.75/0.73  % SZS output start Proof for theBenchmark
% 2.75/0.74  fof(f1775,plain,(
% 2.75/0.74    $false),
% 2.75/0.74    inference(avatar_sat_refutation,[],[f248,f1772])).
% 2.75/0.74  fof(f1772,plain,(
% 2.75/0.74    ~spl4_7),
% 2.75/0.74    inference(avatar_contradiction_clause,[],[f1771])).
% 2.75/0.74  fof(f1771,plain,(
% 2.75/0.74    $false | ~spl4_7),
% 2.75/0.74    inference(subsumption_resolution,[],[f1770,f66])).
% 2.75/0.74  fof(f66,plain,(
% 2.75/0.74    k2_funct_1(sK2) != sK3),
% 2.75/0.74    inference(cnf_transformation,[],[f50])).
% 2.75/0.74  fof(f50,plain,(
% 2.75/0.74    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.75/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f49,f48])).
% 2.75/0.74  fof(f48,plain,(
% 2.75/0.74    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.75/0.74    introduced(choice_axiom,[])).
% 2.75/0.74  fof(f49,plain,(
% 2.75/0.74    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.75/0.74    introduced(choice_axiom,[])).
% 2.75/0.74  fof(f24,plain,(
% 2.75/0.74    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.75/0.74    inference(flattening,[],[f23])).
% 2.75/0.74  fof(f23,plain,(
% 2.75/0.74    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.75/0.74    inference(ennf_transformation,[],[f22])).
% 2.75/0.74  fof(f22,negated_conjecture,(
% 2.75/0.74    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.75/0.74    inference(negated_conjecture,[],[f21])).
% 2.75/0.74  fof(f21,conjecture,(
% 2.75/0.74    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.75/0.74  fof(f1770,plain,(
% 2.75/0.74    k2_funct_1(sK2) = sK3 | ~spl4_7),
% 2.75/0.74    inference(forward_demodulation,[],[f1769,f187])).
% 2.75/0.74  fof(f187,plain,(
% 2.75/0.74    sK3 = k7_relat_1(sK3,sK1)),
% 2.75/0.74    inference(subsumption_resolution,[],[f182,f113])).
% 2.75/0.74  fof(f113,plain,(
% 2.75/0.74    v1_relat_1(sK3)),
% 2.75/0.74    inference(resolution,[],[f88,f60])).
% 2.75/0.74  fof(f60,plain,(
% 2.75/0.74    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.75/0.74    inference(cnf_transformation,[],[f50])).
% 2.75/0.74  fof(f88,plain,(
% 2.75/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f37])).
% 2.75/0.74  fof(f37,plain,(
% 2.75/0.74    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/0.74    inference(ennf_transformation,[],[f13])).
% 2.75/0.74  fof(f13,axiom,(
% 2.75/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.75/0.74  fof(f182,plain,(
% 2.75/0.74    sK3 = k7_relat_1(sK3,sK1) | ~v1_relat_1(sK3)),
% 2.75/0.74    inference(resolution,[],[f84,f168])).
% 2.75/0.74  fof(f168,plain,(
% 2.75/0.74    v4_relat_1(sK3,sK1)),
% 2.75/0.74    inference(resolution,[],[f90,f60])).
% 2.75/0.74  fof(f90,plain,(
% 2.75/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f39])).
% 2.75/0.74  fof(f39,plain,(
% 2.75/0.74    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/0.74    inference(ennf_transformation,[],[f14])).
% 2.75/0.74  fof(f14,axiom,(
% 2.75/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.75/0.74  fof(f84,plain,(
% 2.75/0.74    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f36])).
% 2.75/0.74  fof(f36,plain,(
% 2.75/0.74    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.75/0.74    inference(flattening,[],[f35])).
% 2.75/0.74  fof(f35,plain,(
% 2.75/0.74    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.75/0.74    inference(ennf_transformation,[],[f3])).
% 2.75/0.74  fof(f3,axiom,(
% 2.75/0.74    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.75/0.74  fof(f1769,plain,(
% 2.75/0.74    k2_funct_1(sK2) = k7_relat_1(sK3,sK1) | ~spl4_7),
% 2.75/0.74    inference(forward_demodulation,[],[f1768,f1166])).
% 2.75/0.74  fof(f1166,plain,(
% 2.75/0.74    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_7),
% 2.75/0.74    inference(backward_demodulation,[],[f495,f1141])).
% 2.75/0.74  fof(f1141,plain,(
% 2.75/0.74    sK0 = k1_relat_1(sK2) | ~spl4_7),
% 2.75/0.74    inference(subsumption_resolution,[],[f1137,f167])).
% 2.75/0.74  fof(f167,plain,(
% 2.75/0.74    v4_relat_1(sK2,sK0)),
% 2.75/0.74    inference(resolution,[],[f90,f57])).
% 2.75/0.74  fof(f57,plain,(
% 2.75/0.74    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.75/0.74    inference(cnf_transformation,[],[f50])).
% 2.75/0.74  fof(f1137,plain,(
% 2.75/0.74    sK0 = k1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | ~spl4_7),
% 2.75/0.74    inference(resolution,[],[f1136,f370])).
% 2.75/0.74  fof(f370,plain,(
% 2.75/0.74    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK2)) | k1_relat_1(sK2) = X1 | ~v4_relat_1(sK2,X1)) ) | ~spl4_7),
% 2.75/0.74    inference(resolution,[],[f357,f87])).
% 2.75/0.74  fof(f87,plain,(
% 2.75/0.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f53])).
% 2.75/0.74  fof(f53,plain,(
% 2.75/0.74    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.75/0.74    inference(flattening,[],[f52])).
% 2.75/0.74  fof(f52,plain,(
% 2.75/0.74    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.75/0.74    inference(nnf_transformation,[],[f1])).
% 2.75/0.74  fof(f1,axiom,(
% 2.75/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.75/0.74  fof(f357,plain,(
% 2.75/0.74    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_7),
% 2.75/0.74    inference(resolution,[],[f351,f116])).
% 2.75/0.74  fof(f116,plain,(
% 2.75/0.74    ( ! [X0,X1] : (~v4_relat_1(k6_partfun1(X0),X1) | r1_tarski(X0,X1)) )),
% 2.75/0.74    inference(subsumption_resolution,[],[f115,f101])).
% 2.75/0.74  fof(f101,plain,(
% 2.75/0.74    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.75/0.74    inference(definition_unfolding,[],[f69,f67])).
% 2.75/0.74  fof(f67,plain,(
% 2.75/0.74    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f20])).
% 2.75/0.74  fof(f20,axiom,(
% 2.75/0.74    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.75/0.74  fof(f69,plain,(
% 2.75/0.74    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.75/0.74    inference(cnf_transformation,[],[f10])).
% 2.75/0.74  fof(f10,axiom,(
% 2.75/0.74    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.75/0.74  fof(f115,plain,(
% 2.75/0.74    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v4_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(k6_partfun1(X0))) )),
% 2.75/0.74    inference(superposition,[],[f82,f103])).
% 2.75/0.74  fof(f103,plain,(
% 2.75/0.74    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.75/0.74    inference(definition_unfolding,[],[f71,f67])).
% 2.75/0.74  fof(f71,plain,(
% 2.75/0.74    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.75/0.74    inference(cnf_transformation,[],[f5])).
% 2.75/0.74  fof(f5,axiom,(
% 2.75/0.74    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.75/0.74  fof(f82,plain,(
% 2.75/0.74    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f51])).
% 2.75/0.74  fof(f51,plain,(
% 2.75/0.74    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.75/0.74    inference(nnf_transformation,[],[f34])).
% 2.75/0.74  fof(f34,plain,(
% 2.75/0.74    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.75/0.74    inference(ennf_transformation,[],[f2])).
% 2.75/0.74  fof(f2,axiom,(
% 2.75/0.74    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.75/0.74  fof(f351,plain,(
% 2.75/0.74    ( ! [X0] : (v4_relat_1(k6_partfun1(k1_relat_1(sK2)),X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_7),
% 2.75/0.74    inference(subsumption_resolution,[],[f350,f112])).
% 2.75/0.74  fof(f112,plain,(
% 2.75/0.74    v1_relat_1(sK2)),
% 2.75/0.74    inference(resolution,[],[f88,f57])).
% 2.75/0.74  fof(f350,plain,(
% 2.75/0.74    ( ! [X0] : (v4_relat_1(k6_partfun1(k1_relat_1(sK2)),X0) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl4_7),
% 2.75/0.74    inference(subsumption_resolution,[],[f349,f230])).
% 2.75/0.74  fof(f230,plain,(
% 2.75/0.74    v1_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 2.75/0.74    inference(avatar_component_clause,[],[f229])).
% 2.75/0.74  fof(f229,plain,(
% 2.75/0.74    spl4_7 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.75/0.74  fof(f349,plain,(
% 2.75/0.74    ( ! [X0] : (v4_relat_1(k6_partfun1(k1_relat_1(sK2)),X0) | ~v1_relat_1(k2_funct_1(sK2)) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) )),
% 2.75/0.74    inference(superposition,[],[f93,f320])).
% 2.75/0.74  fof(f320,plain,(
% 2.75/0.74    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))),
% 2.75/0.74    inference(subsumption_resolution,[],[f319,f112])).
% 2.75/0.74  fof(f319,plain,(
% 2.75/0.74    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 2.75/0.74    inference(subsumption_resolution,[],[f317,f55])).
% 2.75/0.74  fof(f55,plain,(
% 2.75/0.74    v1_funct_1(sK2)),
% 2.75/0.74    inference(cnf_transformation,[],[f50])).
% 2.75/0.74  fof(f317,plain,(
% 2.75/0.74    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.75/0.74    inference(resolution,[],[f106,f63])).
% 2.75/0.74  fof(f63,plain,(
% 2.75/0.74    v2_funct_1(sK2)),
% 2.75/0.74    inference(cnf_transformation,[],[f50])).
% 2.75/0.74  fof(f106,plain,(
% 2.75/0.74    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.75/0.74    inference(definition_unfolding,[],[f79,f67])).
% 2.75/0.74  fof(f79,plain,(
% 2.75/0.74    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f32])).
% 2.75/0.74  fof(f32,plain,(
% 2.75/0.74    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.75/0.74    inference(flattening,[],[f31])).
% 2.75/0.74  fof(f31,plain,(
% 2.75/0.74    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.75/0.74    inference(ennf_transformation,[],[f12])).
% 2.75/0.74  fof(f12,axiom,(
% 2.75/0.74    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.75/0.74  fof(f93,plain,(
% 2.75/0.74    ( ! [X2,X0,X1] : (v4_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f41])).
% 2.75/0.74  fof(f41,plain,(
% 2.75/0.74    ! [X0,X1,X2] : ((v4_relat_1(k5_relat_1(X1,X2),X0) & v1_relat_1(k5_relat_1(X1,X2))) | ~v1_relat_1(X2) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.75/0.74    inference(flattening,[],[f40])).
% 2.75/0.74  fof(f40,plain,(
% 2.75/0.74    ! [X0,X1,X2] : ((v4_relat_1(k5_relat_1(X1,X2),X0) & v1_relat_1(k5_relat_1(X1,X2))) | (~v1_relat_1(X2) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.75/0.74    inference(ennf_transformation,[],[f9])).
% 2.75/0.74  fof(f9,axiom,(
% 2.75/0.74    ! [X0,X1,X2] : ((v1_relat_1(X2) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v4_relat_1(k5_relat_1(X1,X2),X0) & v1_relat_1(k5_relat_1(X1,X2))))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc26_relat_1)).
% 2.75/0.74  fof(f1136,plain,(
% 2.75/0.74    r1_tarski(sK0,k1_relat_1(sK2))),
% 2.75/0.74    inference(subsumption_resolution,[],[f1135,f112])).
% 2.75/0.74  fof(f1135,plain,(
% 2.75/0.74    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 2.75/0.74    inference(resolution,[],[f1109,f118])).
% 2.75/0.74  fof(f118,plain,(
% 2.75/0.74    ( ! [X2] : (v4_relat_1(X2,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 2.75/0.74    inference(resolution,[],[f83,f108])).
% 2.75/0.74  fof(f108,plain,(
% 2.75/0.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.75/0.74    inference(equality_resolution,[],[f86])).
% 2.75/0.74  fof(f86,plain,(
% 2.75/0.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.75/0.74    inference(cnf_transformation,[],[f53])).
% 2.75/0.74  fof(f83,plain,(
% 2.75/0.74    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f51])).
% 2.75/0.74  fof(f1109,plain,(
% 2.75/0.74    ( ! [X0] : (~v4_relat_1(sK2,X0) | r1_tarski(sK0,X0)) )),
% 2.75/0.74    inference(resolution,[],[f1049,f116])).
% 2.75/0.74  fof(f1049,plain,(
% 2.75/0.74    ( ! [X1] : (v4_relat_1(k6_partfun1(sK0),X1) | ~v4_relat_1(sK2,X1)) )),
% 2.75/0.74    inference(subsumption_resolution,[],[f1048,f112])).
% 2.75/0.74  fof(f1048,plain,(
% 2.75/0.74    ( ! [X1] : (v4_relat_1(k6_partfun1(sK0),X1) | ~v4_relat_1(sK2,X1) | ~v1_relat_1(sK2)) )),
% 2.75/0.74    inference(subsumption_resolution,[],[f1047,f113])).
% 2.75/0.74  fof(f1047,plain,(
% 2.75/0.74    ( ! [X1] : (v4_relat_1(k6_partfun1(sK0),X1) | ~v1_relat_1(sK3) | ~v4_relat_1(sK2,X1) | ~v1_relat_1(sK2)) )),
% 2.75/0.74    inference(superposition,[],[f93,f1031])).
% 2.75/0.74  fof(f1031,plain,(
% 2.75/0.74    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.75/0.74    inference(global_subsumption,[],[f1014,f1030])).
% 2.75/0.74  fof(f1030,plain,(
% 2.75/0.74    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.75/0.74    inference(resolution,[],[f998,f347])).
% 2.75/0.74  fof(f347,plain,(
% 2.75/0.74    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.75/0.74    inference(resolution,[],[f94,f99])).
% 2.90/0.74  fof(f99,plain,(
% 2.90/0.74    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.90/0.74    inference(definition_unfolding,[],[f68,f67])).
% 2.90/0.74  fof(f68,plain,(
% 2.90/0.74    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.90/0.74    inference(cnf_transformation,[],[f17])).
% 2.90/0.74  fof(f17,axiom,(
% 2.90/0.74    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.90/0.74  fof(f94,plain,(
% 2.90/0.74    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.74    inference(cnf_transformation,[],[f54])).
% 2.90/0.74  fof(f54,plain,(
% 2.90/0.74    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.74    inference(nnf_transformation,[],[f43])).
% 2.90/0.74  fof(f43,plain,(
% 2.90/0.74    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.74    inference(flattening,[],[f42])).
% 2.90/0.74  fof(f42,plain,(
% 2.90/0.74    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.90/0.74    inference(ennf_transformation,[],[f16])).
% 2.90/0.74  fof(f16,axiom,(
% 2.90/0.74    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.90/0.74  fof(f998,plain,(
% 2.90/0.74    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.90/0.74    inference(backward_demodulation,[],[f62,f699])).
% 2.90/0.74  fof(f699,plain,(
% 2.90/0.74    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.90/0.74    inference(subsumption_resolution,[],[f695,f55])).
% 2.90/0.74  fof(f695,plain,(
% 2.90/0.74    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 2.90/0.74    inference(resolution,[],[f386,f57])).
% 2.90/0.74  fof(f386,plain,(
% 2.90/0.74    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 2.90/0.74    inference(subsumption_resolution,[],[f383,f58])).
% 2.90/0.74  fof(f58,plain,(
% 2.90/0.74    v1_funct_1(sK3)),
% 2.90/0.74    inference(cnf_transformation,[],[f50])).
% 2.90/0.74  fof(f383,plain,(
% 2.90/0.74    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 2.90/0.74    inference(resolution,[],[f96,f60])).
% 2.90/0.74  fof(f96,plain,(
% 2.90/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f45])).
% 2.90/0.74  fof(f45,plain,(
% 2.90/0.74    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.90/0.74    inference(flattening,[],[f44])).
% 2.90/0.74  fof(f44,plain,(
% 2.90/0.74    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.90/0.74    inference(ennf_transformation,[],[f19])).
% 2.90/0.74  fof(f19,axiom,(
% 2.90/0.74    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.90/0.74  fof(f62,plain,(
% 2.90/0.74    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.90/0.74    inference(cnf_transformation,[],[f50])).
% 2.90/0.74  fof(f1014,plain,(
% 2.90/0.74    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.90/0.74    inference(subsumption_resolution,[],[f1013,f55])).
% 2.90/0.74  fof(f1013,plain,(
% 2.90/0.74    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1012,f57])).
% 2.90/0.74  fof(f1012,plain,(
% 2.90/0.74    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1011,f58])).
% 2.90/0.74  fof(f1011,plain,(
% 2.90/0.74    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1001,f60])).
% 2.90/0.74  fof(f1001,plain,(
% 2.90/0.74    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.90/0.74    inference(superposition,[],[f98,f699])).
% 2.90/0.74  fof(f98,plain,(
% 2.90/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f47])).
% 2.90/0.74  fof(f47,plain,(
% 2.90/0.74    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.90/0.74    inference(flattening,[],[f46])).
% 2.90/0.74  fof(f46,plain,(
% 2.90/0.74    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.90/0.74    inference(ennf_transformation,[],[f18])).
% 2.90/0.74  fof(f18,axiom,(
% 2.90/0.74    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.90/0.74  fof(f495,plain,(
% 2.90/0.74    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) | ~spl4_7),
% 2.90/0.74    inference(forward_demodulation,[],[f251,f256])).
% 2.90/0.74  fof(f256,plain,(
% 2.90/0.74    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.90/0.74    inference(subsumption_resolution,[],[f255,f112])).
% 2.90/0.74  fof(f255,plain,(
% 2.90/0.74    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.90/0.74    inference(subsumption_resolution,[],[f253,f55])).
% 2.90/0.74  fof(f253,plain,(
% 2.90/0.74    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.90/0.74    inference(resolution,[],[f78,f63])).
% 2.90/0.74  fof(f78,plain,(
% 2.90/0.74    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f30])).
% 2.90/0.74  fof(f30,plain,(
% 2.90/0.74    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.74    inference(flattening,[],[f29])).
% 2.90/0.74  fof(f29,plain,(
% 2.90/0.74    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.74    inference(ennf_transformation,[],[f11])).
% 2.90/0.74  fof(f11,axiom,(
% 2.90/0.74    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.90/0.74  fof(f251,plain,(
% 2.90/0.74    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) | ~spl4_7),
% 2.90/0.74    inference(resolution,[],[f230,f104])).
% 2.90/0.74  fof(f104,plain,(
% 2.90/0.74    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 2.90/0.74    inference(definition_unfolding,[],[f73,f67])).
% 2.90/0.74  fof(f73,plain,(
% 2.90/0.74    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f25])).
% 2.90/0.74  fof(f25,plain,(
% 2.90/0.74    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.90/0.74    inference(ennf_transformation,[],[f6])).
% 2.90/0.74  fof(f6,axiom,(
% 2.90/0.74    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.90/0.74  fof(f1768,plain,(
% 2.90/0.74    k7_relat_1(sK3,sK1) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_7),
% 2.90/0.74    inference(forward_demodulation,[],[f1767,f191])).
% 2.90/0.74  fof(f191,plain,(
% 2.90/0.74    ( ! [X5] : (k7_relat_1(sK3,X5) = k5_relat_1(k6_partfun1(X5),sK3)) )),
% 2.90/0.74    inference(resolution,[],[f107,f113])).
% 2.90/0.74  fof(f107,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 2.90/0.74    inference(definition_unfolding,[],[f81,f67])).
% 2.90/0.74  fof(f81,plain,(
% 2.90/0.74    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f33])).
% 2.90/0.74  fof(f33,plain,(
% 2.90/0.74    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.90/0.74    inference(ennf_transformation,[],[f7])).
% 2.90/0.74  fof(f7,axiom,(
% 2.90/0.74    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.90/0.74  fof(f1767,plain,(
% 2.90/0.74    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_7),
% 2.90/0.74    inference(forward_demodulation,[],[f1761,f308])).
% 2.90/0.74  fof(f308,plain,(
% 2.90/0.74    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.90/0.74    inference(forward_demodulation,[],[f307,f288])).
% 2.90/0.74  fof(f288,plain,(
% 2.90/0.74    sK1 = k2_relat_1(sK2)),
% 2.90/0.74    inference(forward_demodulation,[],[f285,f61])).
% 2.90/0.74  fof(f61,plain,(
% 2.90/0.74    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.90/0.74    inference(cnf_transformation,[],[f50])).
% 2.90/0.74  fof(f285,plain,(
% 2.90/0.74    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.90/0.74    inference(resolution,[],[f89,f57])).
% 2.90/0.74  fof(f89,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f38])).
% 2.90/0.74  fof(f38,plain,(
% 2.90/0.74    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.74    inference(ennf_transformation,[],[f15])).
% 2.90/0.74  fof(f15,axiom,(
% 2.90/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.90/0.74  fof(f307,plain,(
% 2.90/0.74    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.90/0.74    inference(subsumption_resolution,[],[f306,f112])).
% 2.90/0.74  fof(f306,plain,(
% 2.90/0.74    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 2.90/0.74    inference(subsumption_resolution,[],[f304,f55])).
% 2.90/0.74  fof(f304,plain,(
% 2.90/0.74    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.90/0.74    inference(resolution,[],[f105,f63])).
% 2.90/0.74  fof(f105,plain,(
% 2.90/0.74    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.74    inference(definition_unfolding,[],[f80,f67])).
% 2.90/0.74  fof(f80,plain,(
% 2.90/0.74    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f32])).
% 2.90/0.74  fof(f1761,plain,(
% 2.90/0.74    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) | ~spl4_7),
% 2.90/0.74    inference(resolution,[],[f1556,f230])).
% 2.90/0.74  fof(f1556,plain,(
% 2.90/0.74    ( ! [X73] : (~v1_relat_1(X73) | k5_relat_1(k5_relat_1(X73,sK2),sK3) = k5_relat_1(X73,k6_partfun1(sK0))) )),
% 2.90/0.74    inference(forward_demodulation,[],[f1553,f1031])).
% 2.90/0.74  fof(f1553,plain,(
% 2.90/0.74    ( ! [X73] : (k5_relat_1(k5_relat_1(X73,sK2),sK3) = k5_relat_1(X73,k5_relat_1(sK2,sK3)) | ~v1_relat_1(X73)) )),
% 2.90/0.74    inference(resolution,[],[f338,f112])).
% 2.90/0.74  fof(f338,plain,(
% 2.90/0.74    ( ! [X19,X20] : (~v1_relat_1(X20) | k5_relat_1(k5_relat_1(X19,X20),sK3) = k5_relat_1(X19,k5_relat_1(X20,sK3)) | ~v1_relat_1(X19)) )),
% 2.90/0.74    inference(resolution,[],[f74,f113])).
% 2.90/0.74  fof(f74,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f26])).
% 2.90/0.74  fof(f26,plain,(
% 2.90/0.74    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.90/0.74    inference(ennf_transformation,[],[f4])).
% 2.90/0.74  fof(f4,axiom,(
% 2.90/0.74    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.90/0.74  fof(f248,plain,(
% 2.90/0.74    spl4_7),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f247])).
% 2.90/0.74  fof(f247,plain,(
% 2.90/0.74    $false | spl4_7),
% 2.90/0.74    inference(subsumption_resolution,[],[f246,f112])).
% 2.90/0.74  fof(f246,plain,(
% 2.90/0.74    ~v1_relat_1(sK2) | spl4_7),
% 2.90/0.74    inference(subsumption_resolution,[],[f245,f55])).
% 2.90/0.74  fof(f245,plain,(
% 2.90/0.74    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_7),
% 2.90/0.74    inference(resolution,[],[f231,f75])).
% 2.90/0.74  fof(f75,plain,(
% 2.90/0.74    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f28])).
% 2.90/0.74  fof(f28,plain,(
% 2.90/0.74    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.74    inference(flattening,[],[f27])).
% 2.90/0.74  fof(f27,plain,(
% 2.90/0.74    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.74    inference(ennf_transformation,[],[f8])).
% 2.90/0.74  fof(f8,axiom,(
% 2.90/0.74    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.90/0.74  fof(f231,plain,(
% 2.90/0.74    ~v1_relat_1(k2_funct_1(sK2)) | spl4_7),
% 2.90/0.74    inference(avatar_component_clause,[],[f229])).
% 2.90/0.74  % SZS output end Proof for theBenchmark
% 2.90/0.74  % (3299)------------------------------
% 2.90/0.74  % (3299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.74  % (3299)Termination reason: Refutation
% 2.90/0.74  
% 2.90/0.74  % (3299)Memory used [KB]: 12281
% 2.90/0.74  % (3299)Time elapsed: 0.252 s
% 2.90/0.74  % (3299)------------------------------
% 2.90/0.74  % (3299)------------------------------
% 2.90/0.75  % (3291)Success in time 0.382 s
%------------------------------------------------------------------------------
