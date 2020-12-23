%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  141 (7120 expanded)
%              Number of leaves         :   16 (1335 expanded)
%              Depth                    :   29
%              Number of atoms          :  369 (34223 expanded)
%              Number of equality atoms :   88 (5502 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f517,plain,(
    $false ),
    inference(subsumption_resolution,[],[f516,f513])).

fof(f513,plain,(
    ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f512,f443])).

fof(f443,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f419,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f419,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f418,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f418,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2) ),
    inference(forward_demodulation,[],[f389,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f389,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | v1_xboole_0(sK2) ),
    inference(backward_demodulation,[],[f129,f384])).

fof(f384,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f381,f347])).

fof(f347,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f345,f251])).

fof(f251,plain,(
    v1_funct_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f234,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k4_relat_1(sK2)) ) ),
    inference(resolution,[],[f233,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f233,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f232,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f232,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f76,f195])).

fof(f195,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f145,f54])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_funct_1(sK2) = k4_relat_1(sK2) ) ),
    inference(resolution,[],[f117,f85])).

fof(f117,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f114,f52])).

fof(f114,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f55,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f55,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f345,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f344,f214])).

fof(f214,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f213,f195])).

fof(f213,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f201,f195])).

fof(f201,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f51,f195])).

fof(f51,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f344,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f330,f160])).

fof(f160,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f119,f125])).

fof(f125,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f54,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f119,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f118,f54])).

fof(f118,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f53,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f330,plain,(
    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f298,f321])).

fof(f321,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f210,f54])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f157,f195])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f116,f85])).

fof(f116,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f113,f52])).

fof(f113,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f55,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f298,plain,(
    v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f297,f251])).

fof(f297,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2)))
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f293,f212])).

fof(f212,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f175,f195])).

fof(f175,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f120,f54])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f105,f85])).

fof(f105,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f52,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f293,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(superposition,[],[f73,f283])).

fof(f283,plain,(
    sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f208,f54])).

fof(f208,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK1 = k1_relat_1(k4_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f150,f195])).

fof(f150,plain,(
    ! [X0,X1] :
      ( sK1 = k1_relat_1(k2_funct_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f131,f85])).

fof(f131,plain,
    ( ~ v1_relat_1(sK2)
    | sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f115,f130])).

fof(f130,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f126,f56])).

fof(f56,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f126,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f54,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f115,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f112,f52])).

fof(f112,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f55,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f381,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f328,f160])).

fof(f328,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f290,f321])).

fof(f290,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k4_relat_1(sK2))))) ),
    inference(backward_demodulation,[],[f267,f283])).

fof(f267,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) ),
    inference(subsumption_resolution,[],[f259,f212])).

fof(f259,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) ),
    inference(resolution,[],[f251,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f129,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f54,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f512,plain,(
    ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f479,f504])).

fof(f504,plain,(
    ! [X0] : v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f503,f443])).

fof(f503,plain,(
    ! [X0] : v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f502,f60])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f502,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f467,f58])).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f467,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0) ) ),
    inference(backward_demodulation,[],[f407,f443])).

fof(f407,plain,(
    ! [X0] :
      ( v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0)
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(backward_demodulation,[],[f329,f384])).

fof(f329,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k4_relat_1(sK2),sK1,X0) ) ),
    inference(backward_demodulation,[],[f296,f321])).

fof(f296,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0)
      | v1_funct_2(k4_relat_1(sK2),sK1,X0) ) ),
    inference(subsumption_resolution,[],[f295,f251])).

fof(f295,plain,(
    ! [X0] :
      ( v1_funct_2(k4_relat_1(sK2),sK1,X0)
      | ~ v1_funct_1(k4_relat_1(sK2))
      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f291,f212])).

fof(f291,plain,(
    ! [X0] :
      ( v1_funct_2(k4_relat_1(sK2),sK1,X0)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v1_funct_1(k4_relat_1(sK2))
      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) ) ),
    inference(superposition,[],[f80,f283])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f479,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f430,f443])).

fof(f430,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f429,f96])).

fof(f96,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f429,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f428,f384])).

fof(f428,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f400,f251])).

fof(f400,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f214,f384])).

fof(f516,plain,(
    m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f515,f443])).

fof(f515,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f514,f60])).

fof(f514,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f481,f58])).

fof(f481,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X1)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f436,f443])).

fof(f436,plain,(
    ! [X1] :
      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(forward_demodulation,[],[f405,f96])).

fof(f405,plain,(
    ! [X1] :
      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(backward_demodulation,[],[f327,f384])).

fof(f327,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(backward_demodulation,[],[f289,f321])).

fof(f289,plain,(
    ! [X1] :
      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1) ) ),
    inference(backward_demodulation,[],[f269,f283])).

fof(f269,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X1))) ) ),
    inference(subsumption_resolution,[],[f266,f212])).

fof(f266,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k4_relat_1(sK2))
      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X1))) ) ),
    inference(resolution,[],[f251,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:46:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (15699)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (15696)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (15707)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (15712)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (15698)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (15700)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (15697)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (15706)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (15703)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (15693)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (15704)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (15707)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f517,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f516,f513])).
% 0.22/0.50  fof(f513,plain,(
% 0.22/0.50    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.50    inference(forward_demodulation,[],[f512,f443])).
% 0.22/0.50  fof(f443,plain,(
% 0.22/0.50    k1_xboole_0 = sK2),
% 0.22/0.50    inference(resolution,[],[f419,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.50  fof(f419,plain,(
% 0.22/0.50    v1_xboole_0(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f418,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f389,f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.50  fof(f389,plain,(
% 0.22/0.50    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | v1_xboole_0(sK2)),
% 0.22/0.50    inference(backward_demodulation,[],[f129,f384])).
% 0.22/0.50  fof(f384,plain,(
% 0.22/0.50    k1_xboole_0 = sK1),
% 0.22/0.50    inference(subsumption_resolution,[],[f381,f347])).
% 0.22/0.50  fof(f347,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f345,f251])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    v1_funct_1(k4_relat_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f234,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f23])).
% 0.22/0.50  fof(f23,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k4_relat_1(sK2))) )),
% 0.22/0.50    inference(resolution,[],[f233,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | v1_funct_1(k4_relat_1(sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f232,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2)),
% 0.22/0.50    inference(superposition,[],[f76,f195])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f145,f54])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_funct_1(sK2) = k4_relat_1(sK2)) )),
% 0.22/0.50    inference(resolution,[],[f117,f85])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f114,f52])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f55,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    v2_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.50  fof(f345,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f344,f214])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.22/0.50    inference(forward_demodulation,[],[f213,f195])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.50    inference(forward_demodulation,[],[f201,f195])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ~v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.50    inference(backward_demodulation,[],[f51,f195])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f344,plain,(
% 0.22/0.50    v1_funct_2(k4_relat_1(sK2),sK1,sK0) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(superposition,[],[f330,f160])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(superposition,[],[f119,f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.50    inference(resolution,[],[f54,f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(subsumption_resolution,[],[f118,f54])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.50    inference(resolution,[],[f53,f93])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f330,plain,(
% 0.22/0.50    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))),
% 0.22/0.50    inference(backward_demodulation,[],[f298,f321])).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f210,f54])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f157,f195])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(resolution,[],[f116,f85])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f113,f52])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f55,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.50  fof(f298,plain,(
% 0.22/0.50    v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f297,f251])).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2))) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f293,f212])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    v1_relat_1(k4_relat_1(sK2))),
% 0.22/0.50    inference(backward_demodulation,[],[f175,f195])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f120,f54])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(k2_funct_1(sK2))) )),
% 0.22/0.50    inference(resolution,[],[f105,f85])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f52,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f293,plain,(
% 0.22/0.50    v1_funct_2(k4_relat_1(sK2),sK1,k2_relat_1(k4_relat_1(sK2))) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.22/0.50    inference(superposition,[],[f73,f283])).
% 0.22/0.50  fof(f283,plain,(
% 0.22/0.50    sK1 = k1_relat_1(k4_relat_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f208,f54])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK1 = k1_relat_1(k4_relat_1(sK2))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f150,f195])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sK1 = k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(resolution,[],[f131,f85])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    inference(backward_demodulation,[],[f115,f130])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    sK1 = k2_relat_1(sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f126,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f54,f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f112,f52])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f55,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.50  fof(f381,plain,(
% 0.22/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(superposition,[],[f328,f160])).
% 0.22/0.50  fof(f328,plain,(
% 0.22/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.22/0.50    inference(backward_demodulation,[],[f290,f321])).
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k4_relat_1(sK2)))))),
% 0.22/0.50    inference(backward_demodulation,[],[f267,f283])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))),
% 0.22/0.50    inference(subsumption_resolution,[],[f259,f212])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    ~v1_relat_1(k4_relat_1(sK2)) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))),
% 0.22/0.50    inference(resolution,[],[f251,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK2)),
% 0.22/0.50    inference(resolution,[],[f54,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.50  fof(f512,plain,(
% 0.22/0.50    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f479,f504])).
% 0.22/0.50  fof(f504,plain,(
% 0.22/0.50    ( ! [X0] : (v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f503,f443])).
% 0.22/0.50  fof(f503,plain,(
% 0.22/0.50    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f502,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f502,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f467,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.50  fof(f467,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f407,f443])).
% 0.22/0.50  fof(f407,plain,(
% 0.22/0.50    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f329,f384])).
% 0.22/0.50  fof(f329,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k4_relat_1(sK2),sK1,X0)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f296,f321])).
% 0.22/0.50  fof(f296,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) | v1_funct_2(k4_relat_1(sK2),sK1,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f295,f251])).
% 0.22/0.50  fof(f295,plain,(
% 0.22/0.50    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),sK1,X0) | ~v1_funct_1(k4_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f291,f212])).
% 0.22/0.50  fof(f291,plain,(
% 0.22/0.50    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),sK1,X0) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0)) )),
% 0.22/0.50    inference(superposition,[],[f80,f283])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.50  fof(f479,plain,(
% 0.22/0.50    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.50    inference(backward_demodulation,[],[f430,f443])).
% 0.22/0.50  fof(f430,plain,(
% 0.22/0.50    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f429,f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f429,plain,(
% 0.22/0.50    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f428,f384])).
% 0.22/0.50  fof(f428,plain,(
% 0.22/0.50    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f400,f251])).
% 0.22/0.50  fof(f400,plain,(
% 0.22/0.50    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.22/0.50    inference(backward_demodulation,[],[f214,f384])).
% 0.22/0.50  fof(f516,plain,(
% 0.22/0.50    m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.50    inference(forward_demodulation,[],[f515,f443])).
% 0.22/0.50  fof(f515,plain,(
% 0.22/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f514,f60])).
% 0.22/0.50  fof(f514,plain,(
% 0.22/0.50    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f481,f58])).
% 0.22/0.50  fof(f481,plain,(
% 0.22/0.50    ( ! [X1] : (~r1_tarski(k1_relat_1(k1_xboole_0),X1) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f436,f443])).
% 0.22/0.50  fof(f436,plain,(
% 0.22/0.50    ( ! [X1] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(sK2),X1)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f405,f96])).
% 0.22/0.50  fof(f405,plain,(
% 0.22/0.50    ( ! [X1] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_tarski(k1_relat_1(sK2),X1)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f327,f384])).
% 0.22/0.50  fof(f327,plain,(
% 0.22/0.50    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f289,f321])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    ( ! [X1] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f269,f283])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    ( ! [X1] : (~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X1)))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f266,f212])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    ( ! [X1] : (~v1_relat_1(k4_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X1)))) )),
% 0.22/0.50    inference(resolution,[],[f251,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (15707)------------------------------
% 0.22/0.50  % (15707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15707)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (15707)Memory used [KB]: 1791
% 0.22/0.50  % (15707)Time elapsed: 0.088 s
% 0.22/0.50  % (15707)------------------------------
% 0.22/0.50  % (15707)------------------------------
% 0.22/0.50  % (15692)Success in time 0.136 s
%------------------------------------------------------------------------------
