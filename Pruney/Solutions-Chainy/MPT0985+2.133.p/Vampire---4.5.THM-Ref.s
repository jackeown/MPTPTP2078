%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  129 (1881 expanded)
%              Number of leaves         :   12 ( 446 expanded)
%              Depth                    :   28
%              Number of atoms          :  444 (11455 expanded)
%              Number of equality atoms :  150 (1940 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1385,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1384,f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1384,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1383,f1317])).

fof(f1317,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f1316])).

fof(f1316,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f1315,f1256])).

fof(f1256,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f1130])).

fof(f1130,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f108,f1122])).

fof(f1122,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1121,f74])).

fof(f74,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f54,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1121,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1116,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f1116,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1113,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1113,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1104,f224])).

fof(f224,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f158,f221])).

fof(f221,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f219,f37])).

fof(f219,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f215,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f215,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f209,f36])).

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f209,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f57,f37])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f158,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f157,f74])).

fof(f157,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f156,f35])).

fof(f156,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f155,f38])).

fof(f38,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f155,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f150,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f150,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f149,f74])).

fof(f149,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f148,f35])).

fof(f148,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f142,f38])).

fof(f142,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f88,f100])).

fof(f100,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f98,f37])).

fof(f98,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f56,f39])).

fof(f39,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f88,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f87,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f87,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f83,f48])).

fof(f83,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f45,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1104,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f1074,f40])).

fof(f40,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f1074,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f1059,f221])).

fof(f1059,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f1058,f74])).

fof(f1058,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1057,f35])).

fof(f1057,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1055,f38])).

fof(f1055,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f1001,f50])).

fof(f1001,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) ),
    inference(subsumption_resolution,[],[f1000,f74])).

fof(f1000,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f999,f35])).

fof(f999,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f987,f38])).

fof(f987,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f86,f100])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f85,f47])).

fof(f85,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f82,f48])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f49])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f108,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f103,f74])).

fof(f103,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f43,f100])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1315,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f1240,f1122])).

fof(f1240,plain,
    ( sK1 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f1158])).

fof(f1158,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f368,f1122])).

fof(f368,plain,
    ( sK1 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 != sK1 ),
    inference(resolution,[],[f360,f191])).

fof(f191,plain,
    ( v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2))
    | k1_xboole_0 != sK1 ),
    inference(forward_demodulation,[],[f190,f100])).

fof(f190,plain,
    ( v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2))
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f189,f74])).

fof(f189,plain,
    ( v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2))
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f188,f35])).

fof(f188,plain,
    ( v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2))
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f169,f38])).

fof(f169,plain,
    ( v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2))
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f158,f89])).

fof(f89,plain,(
    ! [X2] :
      ( k1_xboole_0 = k2_funct_1(X2)
      | k1_xboole_0 != k2_relat_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f84,f47])).

fof(f84,plain,(
    ! [X2] :
      ( k1_xboole_0 != k2_relat_1(X2)
      | k1_xboole_0 = k2_funct_1(X2)
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f42,f49])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f360,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(k1_xboole_0,X2,X3)
      | k1_xboole_0 = X3
      | k1_relat_1(k1_xboole_0) = X2 ) ),
    inference(subsumption_resolution,[],[f357,f41])).

fof(f357,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k1_xboole_0) = X2
      | k1_xboole_0 = X3
      | ~ v1_funct_2(k1_xboole_0,X2,X3)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(superposition,[],[f211,f55])).

fof(f211,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X1,k1_xboole_0) = X0
      | k1_xboole_0 = X1
      | ~ v1_funct_2(k1_xboole_0,X0,X1) ) ),
    inference(resolution,[],[f57,f41])).

fof(f1383,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f1310,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_xboole_0,X0)
      | k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f127,f64])).

fof(f64,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f72,f55])).

fof(f72,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f68,f64])).

fof(f68,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1310,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1244,f1122])).

fof(f1244,plain,(
    ~ v1_funct_2(k1_xboole_0,sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f1144])).

fof(f1144,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,sK1,sK0) ),
    inference(backward_demodulation,[],[f201,f1122])).

fof(f201,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,sK0)
    | k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f200,f109])).

fof(f109,plain,
    ( k1_xboole_0 != sK1
    | v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f35,f108])).

fof(f200,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_2(k1_xboole_0,sK1,sK0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f199,f100])).

fof(f199,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f198,f74])).

fof(f198,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f197,f35])).

fof(f197,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f196,f38])).

fof(f196,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f171,f41])).

fof(f171,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k1_xboole_0,sK1,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f40,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (14416)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (14427)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (14422)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (14417)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (14413)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (14414)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (14428)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (14419)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (14425)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (14413)Refutation not found, incomplete strategy% (14413)------------------------------
% 0.21/0.49  % (14413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14413)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14413)Memory used [KB]: 10618
% 0.21/0.49  % (14413)Time elapsed: 0.034 s
% 0.21/0.49  % (14413)------------------------------
% 0.21/0.49  % (14413)------------------------------
% 0.21/0.50  % (14430)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (14412)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (14426)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (14425)Refutation not found, incomplete strategy% (14425)------------------------------
% 0.21/0.50  % (14425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14415)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (14431)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (14412)Refutation not found, incomplete strategy% (14412)------------------------------
% 0.21/0.50  % (14412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14412)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14412)Memory used [KB]: 6396
% 0.21/0.50  % (14412)Time elapsed: 0.077 s
% 0.21/0.50  % (14412)------------------------------
% 0.21/0.50  % (14412)------------------------------
% 0.21/0.50  % (14421)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (14429)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (14430)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (14418)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (14420)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (14425)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14425)Memory used [KB]: 1663
% 0.21/0.51  % (14425)Time elapsed: 0.077 s
% 0.21/0.51  % (14425)------------------------------
% 0.21/0.51  % (14425)------------------------------
% 0.21/0.51  % (14423)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.27/0.52  % SZS output start Proof for theBenchmark
% 1.27/0.52  fof(f1385,plain,(
% 1.27/0.52    $false),
% 1.27/0.52    inference(subsumption_resolution,[],[f1384,f41])).
% 1.27/0.52  fof(f41,plain,(
% 1.27/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f2])).
% 1.27/0.52  fof(f2,axiom,(
% 1.27/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.27/0.52  fof(f1384,plain,(
% 1.27/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.27/0.52    inference(subsumption_resolution,[],[f1383,f1317])).
% 1.27/0.52  fof(f1317,plain,(
% 1.27/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.27/0.52    inference(duplicate_literal_removal,[],[f1316])).
% 1.27/0.52  fof(f1316,plain,(
% 1.27/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.27/0.52    inference(forward_demodulation,[],[f1315,f1256])).
% 1.27/0.52  fof(f1256,plain,(
% 1.27/0.52    k1_xboole_0 = sK2),
% 1.27/0.52    inference(trivial_inequality_removal,[],[f1130])).
% 1.27/0.52  fof(f1130,plain,(
% 1.27/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2),
% 1.27/0.52    inference(backward_demodulation,[],[f108,f1122])).
% 1.27/0.52  fof(f1122,plain,(
% 1.27/0.52    k1_xboole_0 = sK1),
% 1.27/0.52    inference(subsumption_resolution,[],[f1121,f74])).
% 1.27/0.52  fof(f74,plain,(
% 1.27/0.52    v1_relat_1(sK2)),
% 1.27/0.52    inference(resolution,[],[f54,f37])).
% 1.27/0.52  fof(f37,plain,(
% 1.27/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f31,plain,(
% 1.27/0.52    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30])).
% 1.27/0.52  fof(f30,plain,(
% 1.27/0.52    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f16,plain,(
% 1.27/0.52    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.27/0.52    inference(flattening,[],[f15])).
% 1.27/0.52  fof(f15,plain,(
% 1.27/0.52    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.27/0.52    inference(ennf_transformation,[],[f13])).
% 1.27/0.52  fof(f13,negated_conjecture,(
% 1.27/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.27/0.52    inference(negated_conjecture,[],[f12])).
% 1.27/0.52  fof(f12,conjecture,(
% 1.27/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.27/0.52  fof(f54,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f25])).
% 1.27/0.52  fof(f25,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.52    inference(ennf_transformation,[],[f7])).
% 1.27/0.52  fof(f7,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.27/0.52  fof(f1121,plain,(
% 1.27/0.52    k1_xboole_0 = sK1 | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f1116,f35])).
% 1.27/0.52  fof(f35,plain,(
% 1.27/0.52    v1_funct_1(sK2)),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f1116,plain,(
% 1.27/0.52    k1_xboole_0 = sK1 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(resolution,[],[f1113,f48])).
% 1.27/0.52  fof(f48,plain,(
% 1.27/0.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f22])).
% 1.27/0.52  fof(f22,plain,(
% 1.27/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.27/0.52    inference(flattening,[],[f21])).
% 1.27/0.52  fof(f21,plain,(
% 1.27/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.27/0.52    inference(ennf_transformation,[],[f5])).
% 1.27/0.52  fof(f5,axiom,(
% 1.27/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.27/0.52  fof(f1113,plain,(
% 1.27/0.52    ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = sK1),
% 1.27/0.52    inference(subsumption_resolution,[],[f1104,f224])).
% 1.27/0.52  fof(f224,plain,(
% 1.27/0.52    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | k1_xboole_0 = sK1),
% 1.27/0.52    inference(superposition,[],[f158,f221])).
% 1.27/0.52  fof(f221,plain,(
% 1.27/0.52    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.27/0.52    inference(subsumption_resolution,[],[f219,f37])).
% 1.27/0.52  fof(f219,plain,(
% 1.27/0.52    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.27/0.52    inference(superposition,[],[f215,f55])).
% 1.27/0.52  fof(f55,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f26])).
% 1.27/0.52  fof(f26,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.52    inference(ennf_transformation,[],[f8])).
% 1.27/0.52  fof(f8,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.27/0.52  fof(f215,plain,(
% 1.27/0.52    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 1.27/0.52    inference(subsumption_resolution,[],[f209,f36])).
% 1.27/0.52  fof(f36,plain,(
% 1.27/0.52    v1_funct_2(sK2,sK0,sK1)),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f209,plain,(
% 1.27/0.52    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.27/0.52    inference(resolution,[],[f57,f37])).
% 1.27/0.52  fof(f57,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.27/0.52    inference(cnf_transformation,[],[f34])).
% 1.27/0.52  fof(f34,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.52    inference(nnf_transformation,[],[f29])).
% 1.27/0.52  fof(f29,plain,(
% 1.27/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.52    inference(flattening,[],[f28])).
% 1.27/0.52  fof(f28,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.52    inference(ennf_transformation,[],[f10])).
% 1.27/0.52  fof(f10,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.27/0.52  fof(f158,plain,(
% 1.27/0.52    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 1.27/0.52    inference(subsumption_resolution,[],[f157,f74])).
% 1.27/0.52  fof(f157,plain,(
% 1.27/0.52    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f156,f35])).
% 1.27/0.52  fof(f156,plain,(
% 1.27/0.52    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f155,f38])).
% 1.27/0.52  fof(f38,plain,(
% 1.27/0.52    v2_funct_1(sK2)),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f155,plain,(
% 1.27/0.52    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(superposition,[],[f150,f50])).
% 1.27/0.52  fof(f50,plain,(
% 1.27/0.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f24])).
% 1.27/0.52  fof(f24,plain,(
% 1.27/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.27/0.52    inference(flattening,[],[f23])).
% 1.27/0.52  fof(f23,plain,(
% 1.27/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.27/0.52    inference(ennf_transformation,[],[f6])).
% 1.27/0.52  fof(f6,axiom,(
% 1.27/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.27/0.52  fof(f150,plain,(
% 1.27/0.52    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))),
% 1.27/0.52    inference(subsumption_resolution,[],[f149,f74])).
% 1.27/0.52  fof(f149,plain,(
% 1.27/0.52    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f148,f35])).
% 1.27/0.52  fof(f148,plain,(
% 1.27/0.52    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f142,f38])).
% 1.27/0.52  fof(f142,plain,(
% 1.27/0.52    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(superposition,[],[f88,f100])).
% 1.27/0.52  fof(f100,plain,(
% 1.27/0.52    sK1 = k2_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f98,f37])).
% 1.27/0.52  fof(f98,plain,(
% 1.27/0.52    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.27/0.52    inference(superposition,[],[f56,f39])).
% 1.27/0.52  fof(f39,plain,(
% 1.27/0.52    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f56,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f27])).
% 1.27/0.52  fof(f27,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.52    inference(ennf_transformation,[],[f9])).
% 1.27/0.52  fof(f9,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.27/0.52  fof(f88,plain,(
% 1.27/0.52    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f87,f47])).
% 1.27/0.52  fof(f47,plain,(
% 1.27/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f22])).
% 1.27/0.52  fof(f87,plain,(
% 1.27/0.52    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f83,f48])).
% 1.27/0.52  fof(f83,plain,(
% 1.27/0.52    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.27/0.52    inference(superposition,[],[f45,f49])).
% 1.27/0.52  fof(f49,plain,(
% 1.27/0.52    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f24])).
% 1.27/0.52  fof(f45,plain,(
% 1.27/0.52    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f20])).
% 1.27/0.52  fof(f20,plain,(
% 1.27/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.27/0.52    inference(flattening,[],[f19])).
% 1.27/0.52  fof(f19,plain,(
% 1.27/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.27/0.52    inference(ennf_transformation,[],[f11])).
% 1.27/0.52  fof(f11,axiom,(
% 1.27/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.27/0.52  fof(f1104,plain,(
% 1.27/0.52    k1_xboole_0 = sK1 | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.27/0.52    inference(resolution,[],[f1074,f40])).
% 1.27/0.52  fof(f40,plain,(
% 1.27/0.52    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f1074,plain,(
% 1.27/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK1),
% 1.27/0.52    inference(superposition,[],[f1059,f221])).
% 1.27/0.52  fof(f1059,plain,(
% 1.27/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 1.27/0.52    inference(subsumption_resolution,[],[f1058,f74])).
% 1.27/0.52  fof(f1058,plain,(
% 1.27/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f1057,f35])).
% 1.27/0.52  fof(f1057,plain,(
% 1.27/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f1055,f38])).
% 1.27/0.52  fof(f1055,plain,(
% 1.27/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(superposition,[],[f1001,f50])).
% 1.27/0.52  fof(f1001,plain,(
% 1.27/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))),
% 1.27/0.52    inference(subsumption_resolution,[],[f1000,f74])).
% 1.27/0.52  fof(f1000,plain,(
% 1.27/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f999,f35])).
% 1.27/0.52  fof(f999,plain,(
% 1.27/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f987,f38])).
% 1.27/0.52  fof(f987,plain,(
% 1.27/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(superposition,[],[f86,f100])).
% 1.27/0.52  fof(f86,plain,(
% 1.27/0.52    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f85,f47])).
% 1.27/0.52  fof(f85,plain,(
% 1.27/0.52    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f82,f48])).
% 1.27/0.52  fof(f82,plain,(
% 1.27/0.52    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(superposition,[],[f46,f49])).
% 1.27/0.52  fof(f46,plain,(
% 1.27/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f20])).
% 1.27/0.52  fof(f108,plain,(
% 1.27/0.52    k1_xboole_0 = sK2 | k1_xboole_0 != sK1),
% 1.27/0.52    inference(subsumption_resolution,[],[f103,f74])).
% 1.27/0.52  fof(f103,plain,(
% 1.27/0.52    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(superposition,[],[f43,f100])).
% 1.27/0.52  fof(f43,plain,(
% 1.27/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f18])).
% 1.27/0.52  fof(f18,plain,(
% 1.27/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.27/0.52    inference(flattening,[],[f17])).
% 1.27/0.52  fof(f17,plain,(
% 1.27/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.27/0.52    inference(ennf_transformation,[],[f4])).
% 1.27/0.52  fof(f4,axiom,(
% 1.27/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.27/0.52  fof(f1315,plain,(
% 1.27/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.27/0.52    inference(forward_demodulation,[],[f1240,f1122])).
% 1.27/0.52  fof(f1240,plain,(
% 1.27/0.52    sK1 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.27/0.52    inference(trivial_inequality_removal,[],[f1158])).
% 1.27/0.52  fof(f1158,plain,(
% 1.27/0.52    k1_xboole_0 != k1_xboole_0 | sK1 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.27/0.52    inference(backward_demodulation,[],[f368,f1122])).
% 1.27/0.52  fof(f368,plain,(
% 1.27/0.52    sK1 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 != sK1),
% 1.27/0.52    inference(resolution,[],[f360,f191])).
% 1.27/0.52  fof(f191,plain,(
% 1.27/0.52    v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2)) | k1_xboole_0 != sK1),
% 1.27/0.52    inference(forward_demodulation,[],[f190,f100])).
% 1.27/0.52  fof(f190,plain,(
% 1.27/0.52    v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2)) | k1_xboole_0 != k2_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f189,f74])).
% 1.27/0.52  fof(f189,plain,(
% 1.27/0.52    v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2)) | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f188,f35])).
% 1.27/0.52  fof(f188,plain,(
% 1.27/0.52    v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2)) | k1_xboole_0 != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f169,f38])).
% 1.27/0.52  fof(f169,plain,(
% 1.27/0.52    v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2)) | k1_xboole_0 != k2_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(superposition,[],[f158,f89])).
% 1.27/0.52  fof(f89,plain,(
% 1.27/0.52    ( ! [X2] : (k1_xboole_0 = k2_funct_1(X2) | k1_xboole_0 != k2_relat_1(X2) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f84,f47])).
% 1.27/0.52  fof(f84,plain,(
% 1.27/0.52    ( ! [X2] : (k1_xboole_0 != k2_relat_1(X2) | k1_xboole_0 = k2_funct_1(X2) | ~v1_relat_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.27/0.52    inference(superposition,[],[f42,f49])).
% 1.27/0.52  fof(f42,plain,(
% 1.27/0.52    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f18])).
% 1.27/0.52  fof(f360,plain,(
% 1.27/0.52    ( ! [X2,X3] : (~v1_funct_2(k1_xboole_0,X2,X3) | k1_xboole_0 = X3 | k1_relat_1(k1_xboole_0) = X2) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f357,f41])).
% 1.27/0.52  fof(f357,plain,(
% 1.27/0.52    ( ! [X2,X3] : (k1_relat_1(k1_xboole_0) = X2 | k1_xboole_0 = X3 | ~v1_funct_2(k1_xboole_0,X2,X3) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.27/0.52    inference(superposition,[],[f211,f55])).
% 1.27/0.52  fof(f211,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = X0 | k1_xboole_0 = X1 | ~v1_funct_2(k1_xboole_0,X0,X1)) )),
% 1.27/0.52    inference(resolution,[],[f57,f41])).
% 1.27/0.52  fof(f1383,plain,(
% 1.27/0.52    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.27/0.52    inference(resolution,[],[f1310,f129])).
% 1.27/0.52  fof(f129,plain,(
% 1.27/0.52    ( ! [X0,X1] : (v1_funct_2(X1,k1_xboole_0,X0) | k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 1.27/0.52    inference(duplicate_literal_removal,[],[f128])).
% 1.27/0.52  fof(f128,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 1.27/0.52    inference(forward_demodulation,[],[f127,f64])).
% 1.27/0.52  fof(f64,plain,(
% 1.27/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.27/0.52    inference(equality_resolution,[],[f52])).
% 1.27/0.52  fof(f52,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.27/0.52    inference(cnf_transformation,[],[f33])).
% 1.27/0.52  fof(f33,plain,(
% 1.27/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.27/0.52    inference(flattening,[],[f32])).
% 1.27/0.52  fof(f32,plain,(
% 1.27/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.27/0.52    inference(nnf_transformation,[],[f1])).
% 1.27/0.52  fof(f1,axiom,(
% 1.27/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.27/0.52  fof(f127,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 1.27/0.52    inference(superposition,[],[f72,f55])).
% 1.27/0.52  fof(f72,plain,(
% 1.27/0.52    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 1.27/0.52    inference(forward_demodulation,[],[f68,f64])).
% 1.27/0.52  fof(f68,plain,(
% 1.27/0.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.27/0.52    inference(equality_resolution,[],[f60])).
% 1.27/0.52  fof(f60,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f34])).
% 1.27/0.52  fof(f1310,plain,(
% 1.27/0.52    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 1.27/0.52    inference(forward_demodulation,[],[f1244,f1122])).
% 1.27/0.52  fof(f1244,plain,(
% 1.27/0.52    ~v1_funct_2(k1_xboole_0,sK1,sK0)),
% 1.27/0.52    inference(trivial_inequality_removal,[],[f1144])).
% 1.27/0.52  fof(f1144,plain,(
% 1.27/0.52    k1_xboole_0 != k1_xboole_0 | ~v1_funct_2(k1_xboole_0,sK1,sK0)),
% 1.27/0.52    inference(backward_demodulation,[],[f201,f1122])).
% 1.27/0.52  fof(f201,plain,(
% 1.27/0.52    ~v1_funct_2(k1_xboole_0,sK1,sK0) | k1_xboole_0 != sK1),
% 1.27/0.52    inference(subsumption_resolution,[],[f200,f109])).
% 1.27/0.52  fof(f109,plain,(
% 1.27/0.52    k1_xboole_0 != sK1 | v1_funct_1(k1_xboole_0)),
% 1.27/0.52    inference(superposition,[],[f35,f108])).
% 1.27/0.52  fof(f200,plain,(
% 1.27/0.52    k1_xboole_0 != sK1 | ~v1_funct_2(k1_xboole_0,sK1,sK0) | ~v1_funct_1(k1_xboole_0)),
% 1.27/0.52    inference(forward_demodulation,[],[f199,f100])).
% 1.27/0.52  fof(f199,plain,(
% 1.27/0.52    ~v1_funct_2(k1_xboole_0,sK1,sK0) | ~v1_funct_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f198,f74])).
% 1.27/0.52  fof(f198,plain,(
% 1.27/0.52    ~v1_funct_2(k1_xboole_0,sK1,sK0) | ~v1_funct_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f197,f35])).
% 1.27/0.52  fof(f197,plain,(
% 1.27/0.52    ~v1_funct_2(k1_xboole_0,sK1,sK0) | ~v1_funct_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f196,f38])).
% 1.27/0.52  fof(f196,plain,(
% 1.27/0.52    ~v1_funct_2(k1_xboole_0,sK1,sK0) | ~v1_funct_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f171,f41])).
% 1.27/0.52  fof(f171,plain,(
% 1.27/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k1_xboole_0,sK1,sK0) | ~v1_funct_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.27/0.52    inference(superposition,[],[f40,f89])).
% 1.27/0.52  % SZS output end Proof for theBenchmark
% 1.27/0.52  % (14430)------------------------------
% 1.27/0.52  % (14430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (14430)Termination reason: Refutation
% 1.27/0.52  
% 1.27/0.52  % (14430)Memory used [KB]: 1918
% 1.27/0.52  % (14430)Time elapsed: 0.085 s
% 1.27/0.52  % (14430)------------------------------
% 1.27/0.52  % (14430)------------------------------
% 1.27/0.52  % (14411)Success in time 0.157 s
%------------------------------------------------------------------------------
