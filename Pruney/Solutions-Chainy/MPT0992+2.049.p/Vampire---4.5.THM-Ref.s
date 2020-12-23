%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:17 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 467 expanded)
%              Number of leaves         :   23 ( 128 expanded)
%              Depth                    :   13
%              Number of atoms          :  380 (2889 expanded)
%              Number of equality atoms :   81 ( 645 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2842,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f109,f161,f173,f178,f285,f1210,f1341])).

fof(f1341,plain,
    ( spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f1332])).

fof(f1332,plain,
    ( $false
    | spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f104,f162,f1213,f1303,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f1303,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(backward_demodulation,[],[f1227,f1302])).

fof(f1302,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f48,f172])).

fof(f172,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_7
  <=> ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f48,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f1227,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f1213,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1213,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f98,f143])).

fof(f143,plain,(
    ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f45,f47,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f162,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl6_2 ),
    inference(forward_demodulation,[],[f95,f143])).

fof(f95,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f104,plain,
    ( k1_xboole_0 != sK1
    | spl6_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1210,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f1204])).

fof(f1204,plain,
    ( $false
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f1195,f148,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f148,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f145,f143])).

fof(f145,plain,(
    ! [X0] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f45,f47,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f1195,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f156,f1193,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f1193,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f156,f150,f301,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f301,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3 ),
    inference(backward_demodulation,[],[f99,f143])).

fof(f99,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f150,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f138,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f138,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f47,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f156,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f154,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | sP5(X2) ) ),
    inference(cnf_transformation,[],[f86_D])).

fof(f86_D,plain,(
    ! [X2] :
      ( ! [X0] : v1_relat_1(k7_relat_1(X2,X0))
    <=> ~ sP5(X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f154,plain,(
    ~ sP5(sK3) ),
    inference(unit_resulting_resolution,[],[f138,f140,f87])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ sP5(X2) ) ),
    inference(general_splitting,[],[f71,f86_D])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f140,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f47,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f285,plain,
    ( spl6_2
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl6_2
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f179,f265])).

fof(f265,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f264,f187])).

fof(f187,plain,
    ( sK3 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f152,f108])).

fof(f108,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f152,plain,(
    sK3 = k7_relat_1(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f138,f140,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f264,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f162,f196])).

fof(f196,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f181,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f181,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f48,f108])).

fof(f179,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f46,f108])).

fof(f46,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f178,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f47,f169,f61])).

fof(f169,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl6_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f173,plain,
    ( ~ spl6_6
    | spl6_7
    | spl6_4 ),
    inference(avatar_split_clause,[],[f165,f102,f171,f167])).

fof(f165,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2
        | ~ v1_relat_1(sK3) )
    | spl6_4 ),
    inference(superposition,[],[f53,f149])).

fof(f149,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl6_4 ),
    inference(forward_demodulation,[],[f139,f142])).

fof(f142,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f104,f46,f47,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f139,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f47,f62])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f161,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f146,f147])).

fof(f147,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(backward_demodulation,[],[f144,f143])).

fof(f144,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f45,f47,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f146,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl6_1 ),
    inference(backward_demodulation,[],[f91,f143])).

fof(f91,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f109,plain,
    ( ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f49,f106,f102])).

fof(f49,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f50,f97,f93,f89])).

fof(f50,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (3476)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (3458)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (3467)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (3465)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  % (3474)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (3468)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (3476)Refutation not found, incomplete strategy% (3476)------------------------------
% 0.20/0.47  % (3476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (3476)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (3476)Memory used [KB]: 10618
% 0.20/0.47  % (3476)Time elapsed: 0.091 s
% 0.20/0.47  % (3476)------------------------------
% 0.20/0.47  % (3476)------------------------------
% 0.20/0.47  % (3460)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (3457)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (3455)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (3466)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (3453)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (3456)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (3454)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (3454)Refutation not found, incomplete strategy% (3454)------------------------------
% 0.20/0.50  % (3454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3454)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3454)Memory used [KB]: 10618
% 0.20/0.50  % (3454)Time elapsed: 0.093 s
% 0.20/0.50  % (3454)------------------------------
% 0.20/0.50  % (3454)------------------------------
% 0.20/0.50  % (3463)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (3471)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (3462)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (3475)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (3464)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (3473)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.26/0.51  % (3469)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.26/0.52  % (3461)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.26/0.52  % (3465)Refutation found. Thanks to Tanya!
% 1.26/0.52  % SZS status Theorem for theBenchmark
% 1.26/0.52  % SZS output start Proof for theBenchmark
% 1.26/0.52  fof(f2842,plain,(
% 1.26/0.52    $false),
% 1.26/0.52    inference(avatar_sat_refutation,[],[f100,f109,f161,f173,f178,f285,f1210,f1341])).
% 1.26/0.52  fof(f1341,plain,(
% 1.26/0.52    spl6_2 | ~spl6_3 | spl6_4 | ~spl6_7),
% 1.26/0.52    inference(avatar_contradiction_clause,[],[f1332])).
% 1.26/0.52  fof(f1332,plain,(
% 1.26/0.52    $false | (spl6_2 | ~spl6_3 | spl6_4 | ~spl6_7)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f104,f162,f1213,f1303,f67])).
% 1.26/0.52  fof(f67,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f44])).
% 1.26/0.52  fof(f44,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(nnf_transformation,[],[f32])).
% 1.26/0.52  fof(f32,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(flattening,[],[f31])).
% 1.26/0.52  fof(f31,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(ennf_transformation,[],[f12])).
% 1.26/0.52  fof(f12,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.26/0.52  fof(f1303,plain,(
% 1.26/0.52    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (~spl6_3 | ~spl6_7)),
% 1.26/0.52    inference(backward_demodulation,[],[f1227,f1302])).
% 1.26/0.52  fof(f1302,plain,(
% 1.26/0.52    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl6_7),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f48,f172])).
% 1.26/0.52  fof(f172,plain,(
% 1.26/0.52    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2) ) | ~spl6_7),
% 1.26/0.52    inference(avatar_component_clause,[],[f171])).
% 1.26/0.52  fof(f171,plain,(
% 1.26/0.52    spl6_7 <=> ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.26/0.52  fof(f48,plain,(
% 1.26/0.52    r1_tarski(sK2,sK0)),
% 1.26/0.52    inference(cnf_transformation,[],[f40])).
% 1.26/0.52  fof(f40,plain,(
% 1.26/0.52    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.26/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f39])).
% 1.26/0.52  fof(f39,plain,(
% 1.26/0.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f18,plain,(
% 1.26/0.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.26/0.52    inference(flattening,[],[f17])).
% 1.26/0.52  fof(f17,plain,(
% 1.26/0.52    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.26/0.52    inference(ennf_transformation,[],[f16])).
% 1.26/0.52  fof(f16,negated_conjecture,(
% 1.26/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.26/0.52    inference(negated_conjecture,[],[f15])).
% 1.26/0.52  fof(f15,conjecture,(
% 1.26/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.26/0.52  fof(f1227,plain,(
% 1.26/0.52    k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl6_3),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f1213,f62])).
% 1.26/0.52  fof(f62,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f29])).
% 1.26/0.52  fof(f29,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(ennf_transformation,[],[f10])).
% 1.26/0.52  fof(f10,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.26/0.52  fof(f1213,plain,(
% 1.26/0.52    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_3),
% 1.26/0.52    inference(forward_demodulation,[],[f98,f143])).
% 1.26/0.52  fof(f143,plain,(
% 1.26/0.52    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f45,f47,f74])).
% 1.26/0.52  fof(f74,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f36])).
% 1.26/0.52  fof(f36,plain,(
% 1.26/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.26/0.52    inference(flattening,[],[f35])).
% 1.26/0.52  fof(f35,plain,(
% 1.26/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.26/0.52    inference(ennf_transformation,[],[f14])).
% 1.26/0.52  fof(f14,axiom,(
% 1.26/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.26/0.52  fof(f47,plain,(
% 1.26/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.26/0.52    inference(cnf_transformation,[],[f40])).
% 1.26/0.52  fof(f45,plain,(
% 1.26/0.52    v1_funct_1(sK3)),
% 1.26/0.52    inference(cnf_transformation,[],[f40])).
% 1.26/0.52  fof(f98,plain,(
% 1.26/0.52    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_3),
% 1.26/0.52    inference(avatar_component_clause,[],[f97])).
% 1.26/0.52  fof(f97,plain,(
% 1.26/0.52    spl6_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.26/0.52  fof(f162,plain,(
% 1.26/0.52    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl6_2),
% 1.26/0.52    inference(forward_demodulation,[],[f95,f143])).
% 1.26/0.52  fof(f95,plain,(
% 1.26/0.52    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl6_2),
% 1.26/0.52    inference(avatar_component_clause,[],[f93])).
% 1.26/0.52  fof(f93,plain,(
% 1.26/0.52    spl6_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.26/0.52  fof(f104,plain,(
% 1.26/0.52    k1_xboole_0 != sK1 | spl6_4),
% 1.26/0.52    inference(avatar_component_clause,[],[f102])).
% 1.26/0.52  fof(f102,plain,(
% 1.26/0.52    spl6_4 <=> k1_xboole_0 = sK1),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.26/0.52  fof(f1210,plain,(
% 1.26/0.52    spl6_3),
% 1.26/0.52    inference(avatar_contradiction_clause,[],[f1204])).
% 1.26/0.52  fof(f1204,plain,(
% 1.26/0.52    $false | spl6_3),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f1195,f148,f64])).
% 1.26/0.52  fof(f64,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f30])).
% 1.26/0.52  fof(f30,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(ennf_transformation,[],[f9])).
% 1.26/0.52  fof(f9,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.26/0.52  fof(f148,plain,(
% 1.26/0.52    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.26/0.52    inference(backward_demodulation,[],[f145,f143])).
% 1.26/0.52  fof(f145,plain,(
% 1.26/0.52    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f45,f47,f76])).
% 1.26/0.52  fof(f76,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f38,plain,(
% 1.26/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.26/0.52    inference(flattening,[],[f37])).
% 1.26/0.52  fof(f37,plain,(
% 1.26/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.26/0.52    inference(ennf_transformation,[],[f13])).
% 1.26/0.52  fof(f13,axiom,(
% 1.26/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.26/0.52  fof(f1195,plain,(
% 1.26/0.52    ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | spl6_3),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f156,f1193,f54])).
% 1.26/0.52  fof(f54,plain,(
% 1.26/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f41])).
% 1.26/0.52  fof(f41,plain,(
% 1.26/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.26/0.52    inference(nnf_transformation,[],[f23])).
% 1.26/0.52  fof(f23,plain,(
% 1.26/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.26/0.52    inference(ennf_transformation,[],[f3])).
% 1.26/0.52  fof(f3,axiom,(
% 1.26/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.26/0.52  fof(f1193,plain,(
% 1.26/0.52    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | spl6_3),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f156,f150,f301,f60])).
% 1.26/0.52  fof(f60,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f27])).
% 1.26/0.52  fof(f27,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.26/0.52    inference(flattening,[],[f26])).
% 1.26/0.52  fof(f26,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.26/0.52    inference(ennf_transformation,[],[f11])).
% 1.26/0.52  fof(f11,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.26/0.52  fof(f301,plain,(
% 1.26/0.52    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl6_3),
% 1.26/0.52    inference(backward_demodulation,[],[f99,f143])).
% 1.26/0.52  fof(f99,plain,(
% 1.26/0.52    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl6_3),
% 1.26/0.52    inference(avatar_component_clause,[],[f97])).
% 1.26/0.52  fof(f150,plain,(
% 1.26/0.52    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)) )),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f138,f52])).
% 1.26/0.52  fof(f52,plain,(
% 1.26/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f20])).
% 1.26/0.52  fof(f20,plain,(
% 1.26/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.26/0.52    inference(ennf_transformation,[],[f6])).
% 1.26/0.52  fof(f6,axiom,(
% 1.26/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.26/0.52  fof(f138,plain,(
% 1.26/0.52    v1_relat_1(sK3)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f47,f61])).
% 1.26/0.52  fof(f61,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f28])).
% 1.26/0.52  fof(f28,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(ennf_transformation,[],[f8])).
% 1.26/0.52  fof(f8,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.26/0.52  fof(f156,plain,(
% 1.26/0.52    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f154,f86])).
% 1.26/0.52  fof(f86,plain,(
% 1.26/0.52    ( ! [X2,X0] : (v1_relat_1(k7_relat_1(X2,X0)) | sP5(X2)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f86_D])).
% 1.26/0.52  fof(f86_D,plain,(
% 1.26/0.52    ( ! [X2] : (( ! [X0] : v1_relat_1(k7_relat_1(X2,X0)) ) <=> ~sP5(X2)) )),
% 1.26/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.26/0.52  fof(f154,plain,(
% 1.26/0.52    ~sP5(sK3)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f138,f140,f87])).
% 1.26/0.52  fof(f87,plain,(
% 1.26/0.52    ( ! [X2,X1] : (~v4_relat_1(X2,X1) | ~v1_relat_1(X2) | ~sP5(X2)) )),
% 1.26/0.52    inference(general_splitting,[],[f71,f86_D])).
% 1.26/0.52  fof(f71,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f34])).
% 1.26/0.52  fof(f34,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 1.26/0.52    inference(flattening,[],[f33])).
% 1.26/0.52  fof(f33,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 1.26/0.52    inference(ennf_transformation,[],[f4])).
% 1.26/0.52  fof(f4,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).
% 1.26/0.52  fof(f140,plain,(
% 1.26/0.52    v4_relat_1(sK3,sK0)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f47,f63])).
% 1.26/0.52  fof(f63,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f30])).
% 1.26/0.52  fof(f285,plain,(
% 1.26/0.52    spl6_2 | ~spl6_5),
% 1.26/0.52    inference(avatar_contradiction_clause,[],[f276])).
% 1.26/0.52  fof(f276,plain,(
% 1.26/0.52    $false | (spl6_2 | ~spl6_5)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f179,f265])).
% 1.26/0.52  fof(f265,plain,(
% 1.26/0.52    ~v1_funct_2(sK3,k1_xboole_0,sK1) | (spl6_2 | ~spl6_5)),
% 1.26/0.52    inference(forward_demodulation,[],[f264,f187])).
% 1.26/0.52  fof(f187,plain,(
% 1.26/0.52    sK3 = k7_relat_1(sK3,k1_xboole_0) | ~spl6_5),
% 1.26/0.52    inference(backward_demodulation,[],[f152,f108])).
% 1.26/0.52  fof(f108,plain,(
% 1.26/0.52    k1_xboole_0 = sK0 | ~spl6_5),
% 1.26/0.52    inference(avatar_component_clause,[],[f106])).
% 1.26/0.52  fof(f106,plain,(
% 1.26/0.52    spl6_5 <=> k1_xboole_0 = sK0),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.26/0.52  fof(f152,plain,(
% 1.26/0.52    sK3 = k7_relat_1(sK3,sK0)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f138,f140,f56])).
% 1.26/0.52  fof(f56,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f25])).
% 1.26/0.52  fof(f25,plain,(
% 1.26/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.26/0.52    inference(flattening,[],[f24])).
% 1.26/0.52  fof(f24,plain,(
% 1.26/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.26/0.52    inference(ennf_transformation,[],[f5])).
% 1.26/0.52  fof(f5,axiom,(
% 1.26/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.26/0.52  fof(f264,plain,(
% 1.26/0.52    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | (spl6_2 | ~spl6_5)),
% 1.26/0.52    inference(forward_demodulation,[],[f162,f196])).
% 1.26/0.52  fof(f196,plain,(
% 1.26/0.52    k1_xboole_0 = sK2 | ~spl6_5),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f181,f51])).
% 1.26/0.52  fof(f51,plain,(
% 1.26/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f19])).
% 1.26/0.52  fof(f19,plain,(
% 1.26/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.26/0.52    inference(ennf_transformation,[],[f1])).
% 1.26/0.52  fof(f1,axiom,(
% 1.26/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.26/0.52  fof(f181,plain,(
% 1.26/0.52    r1_tarski(sK2,k1_xboole_0) | ~spl6_5),
% 1.26/0.52    inference(backward_demodulation,[],[f48,f108])).
% 1.26/0.52  fof(f179,plain,(
% 1.26/0.52    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl6_5),
% 1.26/0.52    inference(backward_demodulation,[],[f46,f108])).
% 1.26/0.52  fof(f46,plain,(
% 1.26/0.52    v1_funct_2(sK3,sK0,sK1)),
% 1.26/0.52    inference(cnf_transformation,[],[f40])).
% 1.26/0.52  fof(f178,plain,(
% 1.26/0.52    spl6_6),
% 1.26/0.52    inference(avatar_contradiction_clause,[],[f176])).
% 1.26/0.52  fof(f176,plain,(
% 1.26/0.52    $false | spl6_6),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f47,f169,f61])).
% 1.26/0.52  fof(f169,plain,(
% 1.26/0.52    ~v1_relat_1(sK3) | spl6_6),
% 1.26/0.52    inference(avatar_component_clause,[],[f167])).
% 1.26/0.52  fof(f167,plain,(
% 1.26/0.52    spl6_6 <=> v1_relat_1(sK3)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.26/0.52  fof(f173,plain,(
% 1.26/0.52    ~spl6_6 | spl6_7 | spl6_4),
% 1.26/0.52    inference(avatar_split_clause,[],[f165,f102,f171,f167])).
% 1.26/0.52  fof(f165,plain,(
% 1.26/0.52    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2 | ~v1_relat_1(sK3)) ) | spl6_4),
% 1.26/0.52    inference(superposition,[],[f53,f149])).
% 1.26/0.52  fof(f149,plain,(
% 1.26/0.52    sK0 = k1_relat_1(sK3) | spl6_4),
% 1.26/0.52    inference(forward_demodulation,[],[f139,f142])).
% 1.26/0.52  fof(f142,plain,(
% 1.26/0.52    sK0 = k1_relset_1(sK0,sK1,sK3) | spl6_4),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f104,f46,f47,f65])).
% 1.26/0.53  fof(f65,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.53    inference(cnf_transformation,[],[f44])).
% 1.26/0.53  fof(f139,plain,(
% 1.26/0.53    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.26/0.53    inference(unit_resulting_resolution,[],[f47,f62])).
% 1.26/0.53  fof(f53,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f22])).
% 1.26/0.53  fof(f22,plain,(
% 1.26/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.26/0.53    inference(flattening,[],[f21])).
% 1.26/0.53  fof(f21,plain,(
% 1.26/0.53    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.26/0.53    inference(ennf_transformation,[],[f7])).
% 1.26/0.53  fof(f7,axiom,(
% 1.26/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.26/0.53  fof(f161,plain,(
% 1.26/0.53    spl6_1),
% 1.26/0.53    inference(avatar_contradiction_clause,[],[f159])).
% 1.26/0.53  fof(f159,plain,(
% 1.26/0.53    $false | spl6_1),
% 1.26/0.53    inference(unit_resulting_resolution,[],[f146,f147])).
% 1.26/0.53  fof(f147,plain,(
% 1.26/0.53    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.26/0.53    inference(backward_demodulation,[],[f144,f143])).
% 1.26/0.53  fof(f144,plain,(
% 1.26/0.53    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.26/0.53    inference(unit_resulting_resolution,[],[f45,f47,f75])).
% 1.26/0.53  fof(f75,plain,(
% 1.26/0.53    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f38])).
% 1.26/0.53  fof(f146,plain,(
% 1.26/0.53    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl6_1),
% 1.26/0.53    inference(backward_demodulation,[],[f91,f143])).
% 1.26/0.53  fof(f91,plain,(
% 1.26/0.53    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl6_1),
% 1.26/0.53    inference(avatar_component_clause,[],[f89])).
% 1.26/0.53  fof(f89,plain,(
% 1.26/0.53    spl6_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.26/0.53  fof(f109,plain,(
% 1.26/0.53    ~spl6_4 | spl6_5),
% 1.26/0.53    inference(avatar_split_clause,[],[f49,f106,f102])).
% 1.26/0.53  fof(f49,plain,(
% 1.26/0.53    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.26/0.53    inference(cnf_transformation,[],[f40])).
% 1.26/0.53  fof(f100,plain,(
% 1.26/0.53    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 1.26/0.53    inference(avatar_split_clause,[],[f50,f97,f93,f89])).
% 1.26/0.53  fof(f50,plain,(
% 1.26/0.53    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.26/0.53    inference(cnf_transformation,[],[f40])).
% 1.26/0.53  % SZS output end Proof for theBenchmark
% 1.26/0.53  % (3465)------------------------------
% 1.26/0.53  % (3465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (3465)Termination reason: Refutation
% 1.26/0.53  
% 1.26/0.53  % (3465)Memory used [KB]: 12025
% 1.26/0.53  % (3465)Time elapsed: 0.096 s
% 1.26/0.53  % (3465)------------------------------
% 1.26/0.53  % (3465)------------------------------
% 1.33/0.53  % (3448)Success in time 0.176 s
%------------------------------------------------------------------------------
