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
% DateTime   : Thu Dec  3 13:03:18 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 617 expanded)
%              Number of leaves         :   26 ( 162 expanded)
%              Depth                    :   18
%              Number of atoms          :  470 (3709 expanded)
%              Number of equality atoms :  100 ( 833 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1266,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f120,f186,f317,f397,f1146,f1163,f1167,f1182,f1219,f1225,f1230,f1265])).

fof(f1265,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f1264])).

fof(f1264,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f1263,f1234])).

fof(f1234,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f109,f141])).

fof(f141,plain,(
    ! [X1] : k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) ),
    inference(subsumption_resolution,[],[f133,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f44])).

fof(f44,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f133,plain,(
    ! [X1] :
      ( k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f55,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f109,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1263,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f1262,f115])).

fof(f115,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1262,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f1261,f207])).

fof(f207,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(backward_demodulation,[],[f106,f141])).

fof(f106,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1261,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(trivial_inequality_removal,[],[f1260])).

fof(f1260,plain,
    ( sK2 != sK2
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(superposition,[],[f82,f1246])).

fof(f1246,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f1241,f475])).

fof(f475,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_22 ),
    inference(resolution,[],[f445,f56])).

fof(f56,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f445,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f444,f144])).

fof(f144,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f139,f61])).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f139,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f55,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f444,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl4_22 ),
    inference(superposition,[],[f64,f443])).

fof(f443,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f137,f316])).

fof(f316,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl4_22
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f137,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f55,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f1241,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f1234,f77])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f1230,plain,(
    spl4_41 ),
    inference(avatar_contradiction_clause,[],[f1229])).

fof(f1229,plain,
    ( $false
    | spl4_41 ),
    inference(subsumption_resolution,[],[f1228,f245])).

fof(f245,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f243,f224])).

fof(f224,plain,(
    ! [X9] : v1_relat_1(k7_relat_1(sK3,X9)) ),
    inference(subsumption_resolution,[],[f219,f61])).

fof(f219,plain,(
    ! [X9] :
      ( v1_relat_1(k7_relat_1(sK3,X9))
      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f210,f59])).

fof(f210,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f209,f53])).

fof(f209,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f208,f55])).

fof(f208,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f89,f141])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f243,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f216,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f216,plain,(
    ! [X6] : v5_relat_1(k7_relat_1(sK3,X6),sK1) ),
    inference(resolution,[],[f210,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1228,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_41 ),
    inference(forward_demodulation,[],[f1181,f141])).

fof(f1181,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | spl4_41 ),
    inference(avatar_component_clause,[],[f1179])).

fof(f1179,plain,
    ( spl4_41
  <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f1225,plain,
    ( ~ spl4_22
    | spl4_40 ),
    inference(avatar_contradiction_clause,[],[f1224])).

fof(f1224,plain,
    ( $false
    | ~ spl4_22
    | spl4_40 ),
    inference(subsumption_resolution,[],[f1223,f91])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f1223,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ spl4_22
    | spl4_40 ),
    inference(forward_demodulation,[],[f1222,f475])).

fof(f1222,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_40 ),
    inference(forward_demodulation,[],[f1177,f141])).

fof(f1177,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f1175,plain,
    ( spl4_40
  <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f1219,plain,(
    spl4_39 ),
    inference(avatar_contradiction_clause,[],[f1218])).

fof(f1218,plain,
    ( $false
    | spl4_39 ),
    inference(subsumption_resolution,[],[f1213,f224])).

fof(f1213,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_39 ),
    inference(backward_demodulation,[],[f1173,f141])).

fof(f1173,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f1171,plain,
    ( spl4_39
  <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f1182,plain,
    ( ~ spl4_39
    | ~ spl4_40
    | ~ spl4_41
    | spl4_3 ),
    inference(avatar_split_clause,[],[f1168,f108,f1179,f1175,f1171])).

fof(f1168,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_3 ),
    inference(resolution,[],[f110,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f110,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1167,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f1166,f128,f124])).

fof(f124,plain,
    ( spl4_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f128,plain,
    ( spl4_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1166,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f56,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1163,plain,
    ( spl4_2
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1162])).

fof(f1162,plain,
    ( $false
    | spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1161,f54])).

fof(f54,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f1161,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | spl4_2
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1160,f146])).

fof(f146,plain,(
    sK3 = k7_relat_1(sK3,sK0) ),
    inference(subsumption_resolution,[],[f145,f144])).

fof(f145,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f135,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f135,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f55,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1160,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK0),sK0,sK1)
    | spl4_2
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f207,f130])).

fof(f130,plain,
    ( sK0 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f1146,plain,
    ( spl4_3
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1145])).

fof(f1145,plain,
    ( $false
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1144,f53])).

fof(f1144,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1141,f55])).

fof(f1141,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f1135,f89])).

fof(f1135,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f110,f130])).

fof(f397,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f395,f91])).

fof(f395,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f356,f362])).

fof(f362,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(resolution,[],[f354,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f354,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f56,f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f356,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f126,f119])).

fof(f126,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f317,plain,
    ( spl4_22
    | spl4_4 ),
    inference(avatar_split_clause,[],[f142,f113,f314])).

fof(f142,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f134,f54])).

fof(f134,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f55,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f186,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f140,f102])).

fof(f102,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f140,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f132,f53])).

fof(f132,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f55,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f57,f117,f113])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f58,f108,f104,f100])).

fof(f58,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 09:16:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.51  % (31533)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (31537)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (31553)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (31556)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (31549)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (31546)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (31531)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (31554)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (31552)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.54  % (31544)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (31538)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (31532)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (31534)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (31542)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % (31535)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (31536)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (31547)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (31551)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.55  % (31540)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (31541)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.55  % (31548)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (31555)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.56  % (31543)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.56  % (31550)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.56  % (31545)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (31557)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.71/0.60  % (31532)Refutation found. Thanks to Tanya!
% 1.71/0.60  % SZS status Theorem for theBenchmark
% 1.71/0.60  % SZS output start Proof for theBenchmark
% 1.71/0.60  fof(f1266,plain,(
% 1.71/0.60    $false),
% 1.71/0.60    inference(avatar_sat_refutation,[],[f111,f120,f186,f317,f397,f1146,f1163,f1167,f1182,f1219,f1225,f1230,f1265])).
% 1.71/0.60  fof(f1265,plain,(
% 1.71/0.60    spl4_2 | ~spl4_3 | spl4_4 | ~spl4_22),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f1264])).
% 1.71/0.60  fof(f1264,plain,(
% 1.71/0.60    $false | (spl4_2 | ~spl4_3 | spl4_4 | ~spl4_22)),
% 1.71/0.60    inference(subsumption_resolution,[],[f1263,f1234])).
% 1.71/0.60  fof(f1234,plain,(
% 1.71/0.60    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.71/0.60    inference(forward_demodulation,[],[f109,f141])).
% 1.71/0.60  fof(f141,plain,(
% 1.71/0.60    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)) )),
% 1.71/0.60    inference(subsumption_resolution,[],[f133,f53])).
% 1.71/0.60  fof(f53,plain,(
% 1.71/0.60    v1_funct_1(sK3)),
% 1.71/0.60    inference(cnf_transformation,[],[f45])).
% 1.71/0.60  fof(f45,plain,(
% 1.71/0.60    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.71/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f44])).
% 1.71/0.60  fof(f44,plain,(
% 1.71/0.60    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.71/0.60    introduced(choice_axiom,[])).
% 1.71/0.60  fof(f22,plain,(
% 1.71/0.60    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.71/0.60    inference(flattening,[],[f21])).
% 1.71/0.60  fof(f21,plain,(
% 1.71/0.60    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.71/0.60    inference(ennf_transformation,[],[f20])).
% 1.71/0.60  fof(f20,negated_conjecture,(
% 1.71/0.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.71/0.60    inference(negated_conjecture,[],[f19])).
% 1.71/0.60  fof(f19,conjecture,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.71/0.60  fof(f133,plain,(
% 1.71/0.60    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) | ~v1_funct_1(sK3)) )),
% 1.71/0.60    inference(resolution,[],[f55,f87])).
% 1.71/0.60  fof(f87,plain,(
% 1.71/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f41])).
% 1.71/0.60  fof(f41,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.71/0.60    inference(flattening,[],[f40])).
% 1.71/0.60  fof(f40,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.71/0.60    inference(ennf_transformation,[],[f18])).
% 1.71/0.60  fof(f18,axiom,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.71/0.60  fof(f55,plain,(
% 1.71/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.60    inference(cnf_transformation,[],[f45])).
% 1.71/0.60  fof(f109,plain,(
% 1.71/0.60    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.71/0.60    inference(avatar_component_clause,[],[f108])).
% 1.71/0.60  fof(f108,plain,(
% 1.71/0.60    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.71/0.60  fof(f1263,plain,(
% 1.71/0.60    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | ~spl4_3 | spl4_4 | ~spl4_22)),
% 1.71/0.60    inference(subsumption_resolution,[],[f1262,f115])).
% 1.71/0.60  fof(f115,plain,(
% 1.71/0.60    k1_xboole_0 != sK1 | spl4_4),
% 1.71/0.60    inference(avatar_component_clause,[],[f113])).
% 1.71/0.60  fof(f113,plain,(
% 1.71/0.60    spl4_4 <=> k1_xboole_0 = sK1),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.71/0.60  fof(f1262,plain,(
% 1.71/0.60    k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | ~spl4_3 | ~spl4_22)),
% 1.71/0.60    inference(subsumption_resolution,[],[f1261,f207])).
% 1.71/0.60  fof(f207,plain,(
% 1.71/0.60    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 1.71/0.60    inference(backward_demodulation,[],[f106,f141])).
% 1.71/0.60  fof(f106,plain,(
% 1.71/0.60    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 1.71/0.60    inference(avatar_component_clause,[],[f104])).
% 1.71/0.60  fof(f104,plain,(
% 1.71/0.60    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.71/0.60  fof(f1261,plain,(
% 1.71/0.60    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_3 | ~spl4_22)),
% 1.71/0.60    inference(trivial_inequality_removal,[],[f1260])).
% 1.71/0.60  fof(f1260,plain,(
% 1.71/0.60    sK2 != sK2 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_3 | ~spl4_22)),
% 1.71/0.60    inference(superposition,[],[f82,f1246])).
% 1.71/0.60  fof(f1246,plain,(
% 1.71/0.60    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (~spl4_3 | ~spl4_22)),
% 1.71/0.60    inference(forward_demodulation,[],[f1241,f475])).
% 1.71/0.60  fof(f475,plain,(
% 1.71/0.60    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_22),
% 1.71/0.60    inference(resolution,[],[f445,f56])).
% 1.71/0.60  fof(f56,plain,(
% 1.71/0.60    r1_tarski(sK2,sK0)),
% 1.71/0.60    inference(cnf_transformation,[],[f45])).
% 1.71/0.60  fof(f445,plain,(
% 1.71/0.60    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_22),
% 1.71/0.60    inference(subsumption_resolution,[],[f444,f144])).
% 1.71/0.60  fof(f144,plain,(
% 1.71/0.60    v1_relat_1(sK3)),
% 1.71/0.60    inference(subsumption_resolution,[],[f139,f61])).
% 1.71/0.60  fof(f61,plain,(
% 1.71/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.71/0.60    inference(cnf_transformation,[],[f9])).
% 1.71/0.60  fof(f9,axiom,(
% 1.71/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.71/0.60  fof(f139,plain,(
% 1.71/0.60    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.71/0.60    inference(resolution,[],[f55,f59])).
% 1.71/0.60  fof(f59,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f23])).
% 1.71/0.60  fof(f23,plain,(
% 1.71/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.71/0.60    inference(ennf_transformation,[],[f6])).
% 1.71/0.60  fof(f6,axiom,(
% 1.71/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.71/0.60  fof(f444,plain,(
% 1.71/0.60    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl4_22),
% 1.71/0.60    inference(superposition,[],[f64,f443])).
% 1.71/0.60  fof(f443,plain,(
% 1.71/0.60    sK0 = k1_relat_1(sK3) | ~spl4_22),
% 1.71/0.60    inference(forward_demodulation,[],[f137,f316])).
% 1.71/0.60  fof(f316,plain,(
% 1.71/0.60    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_22),
% 1.71/0.60    inference(avatar_component_clause,[],[f314])).
% 1.71/0.60  fof(f314,plain,(
% 1.71/0.60    spl4_22 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.71/0.60  fof(f137,plain,(
% 1.71/0.60    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.71/0.60    inference(resolution,[],[f55,f77])).
% 1.71/0.60  fof(f77,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f34])).
% 1.71/0.60  fof(f34,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.60    inference(ennf_transformation,[],[f14])).
% 1.71/0.60  fof(f14,axiom,(
% 1.71/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.71/0.60  fof(f64,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f28])).
% 1.71/0.60  fof(f28,plain,(
% 1.71/0.60    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(flattening,[],[f27])).
% 1.71/0.60  fof(f27,plain,(
% 1.71/0.60    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(ennf_transformation,[],[f12])).
% 1.71/0.60  fof(f12,axiom,(
% 1.71/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.71/0.60  fof(f1241,plain,(
% 1.71/0.60    k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl4_3),
% 1.71/0.60    inference(resolution,[],[f1234,f77])).
% 1.71/0.60  fof(f82,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.60    inference(cnf_transformation,[],[f52])).
% 1.71/0.60  fof(f52,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.60    inference(nnf_transformation,[],[f37])).
% 1.71/0.60  fof(f37,plain,(
% 1.71/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.60    inference(flattening,[],[f36])).
% 1.71/0.60  fof(f36,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.60    inference(ennf_transformation,[],[f16])).
% 1.71/0.60  fof(f16,axiom,(
% 1.71/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.71/0.60  fof(f1230,plain,(
% 1.71/0.60    spl4_41),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f1229])).
% 1.71/0.60  fof(f1229,plain,(
% 1.71/0.60    $false | spl4_41),
% 1.71/0.60    inference(subsumption_resolution,[],[f1228,f245])).
% 1.71/0.60  fof(f245,plain,(
% 1.71/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.71/0.60    inference(subsumption_resolution,[],[f243,f224])).
% 1.71/0.60  fof(f224,plain,(
% 1.71/0.60    ( ! [X9] : (v1_relat_1(k7_relat_1(sK3,X9))) )),
% 1.71/0.60    inference(subsumption_resolution,[],[f219,f61])).
% 1.71/0.60  fof(f219,plain,(
% 1.71/0.60    ( ! [X9] : (v1_relat_1(k7_relat_1(sK3,X9)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))) )),
% 1.71/0.60    inference(resolution,[],[f210,f59])).
% 1.71/0.60  fof(f210,plain,(
% 1.71/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.71/0.60    inference(subsumption_resolution,[],[f209,f53])).
% 1.71/0.60  fof(f209,plain,(
% 1.71/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.71/0.60    inference(subsumption_resolution,[],[f208,f55])).
% 1.71/0.60  fof(f208,plain,(
% 1.71/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.71/0.60    inference(superposition,[],[f89,f141])).
% 1.71/0.60  fof(f89,plain,(
% 1.71/0.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f43])).
% 1.71/0.60  fof(f43,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.71/0.60    inference(flattening,[],[f42])).
% 1.71/0.60  fof(f42,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.71/0.60    inference(ennf_transformation,[],[f17])).
% 1.71/0.60  fof(f17,axiom,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.71/0.60  fof(f243,plain,(
% 1.71/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.71/0.60    inference(resolution,[],[f216,f65])).
% 1.71/0.60  fof(f65,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f46])).
% 1.71/0.60  fof(f46,plain,(
% 1.71/0.60    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(nnf_transformation,[],[f29])).
% 1.71/0.60  fof(f29,plain,(
% 1.71/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(ennf_transformation,[],[f7])).
% 1.71/0.60  fof(f7,axiom,(
% 1.71/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.71/0.60  fof(f216,plain,(
% 1.71/0.60    ( ! [X6] : (v5_relat_1(k7_relat_1(sK3,X6),sK1)) )),
% 1.71/0.60    inference(resolution,[],[f210,f79])).
% 1.71/0.60  fof(f79,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f35])).
% 1.71/0.60  fof(f35,plain,(
% 1.71/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.60    inference(ennf_transformation,[],[f13])).
% 1.71/0.60  fof(f13,axiom,(
% 1.71/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.71/0.60  fof(f1228,plain,(
% 1.71/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | spl4_41),
% 1.71/0.60    inference(forward_demodulation,[],[f1181,f141])).
% 1.71/0.60  fof(f1181,plain,(
% 1.71/0.60    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | spl4_41),
% 1.71/0.60    inference(avatar_component_clause,[],[f1179])).
% 1.71/0.60  fof(f1179,plain,(
% 1.71/0.60    spl4_41 <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.71/0.60  fof(f1225,plain,(
% 1.71/0.60    ~spl4_22 | spl4_40),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f1224])).
% 1.71/0.60  fof(f1224,plain,(
% 1.71/0.60    $false | (~spl4_22 | spl4_40)),
% 1.71/0.60    inference(subsumption_resolution,[],[f1223,f91])).
% 1.71/0.60  fof(f91,plain,(
% 1.71/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.71/0.60    inference(equality_resolution,[],[f68])).
% 1.71/0.60  fof(f68,plain,(
% 1.71/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.71/0.60    inference(cnf_transformation,[],[f48])).
% 1.71/0.60  fof(f48,plain,(
% 1.71/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.60    inference(flattening,[],[f47])).
% 1.71/0.60  fof(f47,plain,(
% 1.71/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.60    inference(nnf_transformation,[],[f1])).
% 1.71/0.60  fof(f1,axiom,(
% 1.71/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.71/0.60  fof(f1223,plain,(
% 1.71/0.60    ~r1_tarski(sK2,sK2) | (~spl4_22 | spl4_40)),
% 1.71/0.60    inference(forward_demodulation,[],[f1222,f475])).
% 1.71/0.60  fof(f1222,plain,(
% 1.71/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_40),
% 1.71/0.60    inference(forward_demodulation,[],[f1177,f141])).
% 1.71/0.60  fof(f1177,plain,(
% 1.71/0.60    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | spl4_40),
% 1.71/0.60    inference(avatar_component_clause,[],[f1175])).
% 1.71/0.60  fof(f1175,plain,(
% 1.71/0.60    spl4_40 <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.71/0.60  fof(f1219,plain,(
% 1.71/0.60    spl4_39),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f1218])).
% 1.71/0.60  fof(f1218,plain,(
% 1.71/0.60    $false | spl4_39),
% 1.71/0.60    inference(subsumption_resolution,[],[f1213,f224])).
% 1.71/0.60  fof(f1213,plain,(
% 1.71/0.60    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_39),
% 1.71/0.60    inference(backward_demodulation,[],[f1173,f141])).
% 1.71/0.60  fof(f1173,plain,(
% 1.71/0.60    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_39),
% 1.71/0.60    inference(avatar_component_clause,[],[f1171])).
% 1.71/0.60  fof(f1171,plain,(
% 1.71/0.60    spl4_39 <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.71/0.60  fof(f1182,plain,(
% 1.71/0.60    ~spl4_39 | ~spl4_40 | ~spl4_41 | spl4_3),
% 1.71/0.60    inference(avatar_split_clause,[],[f1168,f108,f1179,f1175,f1171])).
% 1.71/0.60  fof(f1168,plain,(
% 1.71/0.60    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_3),
% 1.71/0.60    inference(resolution,[],[f110,f76])).
% 1.71/0.60  fof(f76,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f33])).
% 1.71/0.60  fof(f33,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.71/0.60    inference(flattening,[],[f32])).
% 1.71/0.60  fof(f32,plain,(
% 1.71/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.71/0.60    inference(ennf_transformation,[],[f15])).
% 1.71/0.60  fof(f15,axiom,(
% 1.71/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.71/0.60  fof(f110,plain,(
% 1.71/0.60    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.71/0.60    inference(avatar_component_clause,[],[f108])).
% 1.71/0.60  fof(f1167,plain,(
% 1.71/0.60    ~spl4_6 | spl4_7),
% 1.71/0.60    inference(avatar_split_clause,[],[f1166,f128,f124])).
% 1.71/0.60  fof(f124,plain,(
% 1.71/0.60    spl4_6 <=> r1_tarski(sK0,sK2)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.71/0.60  fof(f128,plain,(
% 1.71/0.60    spl4_7 <=> sK0 = sK2),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.71/0.60  fof(f1166,plain,(
% 1.71/0.60    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 1.71/0.60    inference(resolution,[],[f56,f70])).
% 1.71/0.60  fof(f70,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f48])).
% 1.71/0.60  fof(f1163,plain,(
% 1.71/0.60    spl4_2 | ~spl4_7),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f1162])).
% 1.71/0.60  fof(f1162,plain,(
% 1.71/0.60    $false | (spl4_2 | ~spl4_7)),
% 1.71/0.60    inference(subsumption_resolution,[],[f1161,f54])).
% 1.71/0.60  fof(f54,plain,(
% 1.71/0.60    v1_funct_2(sK3,sK0,sK1)),
% 1.71/0.60    inference(cnf_transformation,[],[f45])).
% 1.71/0.60  fof(f1161,plain,(
% 1.71/0.60    ~v1_funct_2(sK3,sK0,sK1) | (spl4_2 | ~spl4_7)),
% 1.71/0.60    inference(forward_demodulation,[],[f1160,f146])).
% 1.71/0.60  fof(f146,plain,(
% 1.71/0.60    sK3 = k7_relat_1(sK3,sK0)),
% 1.71/0.60    inference(subsumption_resolution,[],[f145,f144])).
% 1.71/0.60  fof(f145,plain,(
% 1.71/0.60    sK3 = k7_relat_1(sK3,sK0) | ~v1_relat_1(sK3)),
% 1.71/0.60    inference(resolution,[],[f135,f67])).
% 1.71/0.60  fof(f67,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f31])).
% 1.71/0.60  fof(f31,plain,(
% 1.71/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(flattening,[],[f30])).
% 1.71/0.60  fof(f30,plain,(
% 1.71/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.71/0.60    inference(ennf_transformation,[],[f10])).
% 1.71/0.60  fof(f10,axiom,(
% 1.71/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.71/0.60  fof(f135,plain,(
% 1.71/0.60    v4_relat_1(sK3,sK0)),
% 1.71/0.60    inference(resolution,[],[f55,f78])).
% 1.71/0.60  fof(f78,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f35])).
% 1.71/0.60  fof(f1160,plain,(
% 1.71/0.60    ~v1_funct_2(k7_relat_1(sK3,sK0),sK0,sK1) | (spl4_2 | ~spl4_7)),
% 1.71/0.60    inference(forward_demodulation,[],[f207,f130])).
% 1.71/0.60  fof(f130,plain,(
% 1.71/0.60    sK0 = sK2 | ~spl4_7),
% 1.71/0.60    inference(avatar_component_clause,[],[f128])).
% 1.71/0.60  fof(f1146,plain,(
% 1.71/0.60    spl4_3 | ~spl4_7),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f1145])).
% 1.71/0.60  fof(f1145,plain,(
% 1.71/0.60    $false | (spl4_3 | ~spl4_7)),
% 1.71/0.60    inference(subsumption_resolution,[],[f1144,f53])).
% 1.71/0.60  fof(f1144,plain,(
% 1.71/0.60    ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7)),
% 1.71/0.60    inference(subsumption_resolution,[],[f1141,f55])).
% 1.71/0.60  fof(f1141,plain,(
% 1.71/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7)),
% 1.71/0.60    inference(resolution,[],[f1135,f89])).
% 1.71/0.60  fof(f1135,plain,(
% 1.71/0.60    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_7)),
% 1.71/0.60    inference(forward_demodulation,[],[f110,f130])).
% 1.71/0.60  fof(f397,plain,(
% 1.71/0.60    ~spl4_5 | spl4_6),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f396])).
% 1.71/0.60  fof(f396,plain,(
% 1.71/0.60    $false | (~spl4_5 | spl4_6)),
% 1.71/0.60    inference(subsumption_resolution,[],[f395,f91])).
% 1.71/0.60  fof(f395,plain,(
% 1.71/0.60    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl4_5 | spl4_6)),
% 1.71/0.60    inference(backward_demodulation,[],[f356,f362])).
% 1.71/0.60  fof(f362,plain,(
% 1.71/0.60    k1_xboole_0 = sK2 | ~spl4_5),
% 1.71/0.60    inference(resolution,[],[f354,f60])).
% 1.71/0.60  fof(f60,plain,(
% 1.71/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.71/0.60    inference(cnf_transformation,[],[f24])).
% 1.71/0.60  fof(f24,plain,(
% 1.71/0.60    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.71/0.60    inference(ennf_transformation,[],[f3])).
% 1.71/0.60  fof(f3,axiom,(
% 1.71/0.60    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.71/0.60  fof(f354,plain,(
% 1.71/0.60    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 1.71/0.60    inference(backward_demodulation,[],[f56,f119])).
% 1.71/0.60  fof(f119,plain,(
% 1.71/0.60    k1_xboole_0 = sK0 | ~spl4_5),
% 1.71/0.60    inference(avatar_component_clause,[],[f117])).
% 1.71/0.60  fof(f117,plain,(
% 1.71/0.60    spl4_5 <=> k1_xboole_0 = sK0),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.71/0.60  fof(f356,plain,(
% 1.71/0.60    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_5 | spl4_6)),
% 1.71/0.60    inference(backward_demodulation,[],[f126,f119])).
% 1.71/0.60  fof(f126,plain,(
% 1.71/0.60    ~r1_tarski(sK0,sK2) | spl4_6),
% 1.71/0.60    inference(avatar_component_clause,[],[f124])).
% 1.71/0.60  fof(f317,plain,(
% 1.71/0.60    spl4_22 | spl4_4),
% 1.71/0.60    inference(avatar_split_clause,[],[f142,f113,f314])).
% 1.71/0.60  fof(f142,plain,(
% 1.71/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.71/0.60    inference(subsumption_resolution,[],[f134,f54])).
% 1.71/0.60  fof(f134,plain,(
% 1.71/0.60    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.71/0.60    inference(resolution,[],[f55,f80])).
% 1.71/0.60  fof(f80,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.71/0.60    inference(cnf_transformation,[],[f52])).
% 1.71/0.60  fof(f186,plain,(
% 1.71/0.60    spl4_1),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f185])).
% 1.71/0.60  fof(f185,plain,(
% 1.71/0.60    $false | spl4_1),
% 1.71/0.60    inference(resolution,[],[f140,f102])).
% 1.71/0.60  fof(f102,plain,(
% 1.71/0.60    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 1.71/0.60    inference(avatar_component_clause,[],[f100])).
% 1.71/0.60  fof(f100,plain,(
% 1.71/0.60    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.71/0.60  fof(f140,plain,(
% 1.71/0.60    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.71/0.60    inference(subsumption_resolution,[],[f132,f53])).
% 1.71/0.60  fof(f132,plain,(
% 1.71/0.60    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.71/0.60    inference(resolution,[],[f55,f88])).
% 1.71/0.60  fof(f88,plain,(
% 1.71/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f43])).
% 1.71/0.60  fof(f120,plain,(
% 1.71/0.60    ~spl4_4 | spl4_5),
% 1.71/0.60    inference(avatar_split_clause,[],[f57,f117,f113])).
% 1.71/0.60  fof(f57,plain,(
% 1.71/0.60    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.71/0.60    inference(cnf_transformation,[],[f45])).
% 1.71/0.60  fof(f111,plain,(
% 1.71/0.60    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.71/0.60    inference(avatar_split_clause,[],[f58,f108,f104,f100])).
% 1.71/0.60  fof(f58,plain,(
% 1.71/0.60    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.71/0.60    inference(cnf_transformation,[],[f45])).
% 1.71/0.60  % SZS output end Proof for theBenchmark
% 1.71/0.60  % (31532)------------------------------
% 1.71/0.60  % (31532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.60  % (31532)Termination reason: Refutation
% 1.71/0.60  
% 1.71/0.60  % (31532)Memory used [KB]: 11001
% 1.71/0.60  % (31532)Time elapsed: 0.177 s
% 1.71/0.60  % (31532)------------------------------
% 1.71/0.60  % (31532)------------------------------
% 1.71/0.60  % (31526)Success in time 0.229 s
%------------------------------------------------------------------------------
