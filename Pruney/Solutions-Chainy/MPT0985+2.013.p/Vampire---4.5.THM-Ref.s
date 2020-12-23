%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  137 (30755 expanded)
%              Number of leaves         :   14 (7764 expanded)
%              Depth                    :   28
%              Number of atoms          :  399 (191993 expanded)
%              Number of equality atoms :  110 (27781 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f652,plain,(
    $false ),
    inference(subsumption_resolution,[],[f651,f648])).

fof(f648,plain,(
    ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f647,f641])).

fof(f641,plain,(
    ! [X0] : v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f640,f523])).

fof(f523,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f522,f79])).

fof(f79,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f522,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f519,f377])).

fof(f377,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f344,f79])).

fof(f344,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f283,f313])).

fof(f313,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f178,f179,f267,f308])).

fof(f308,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f199,f262])).

fof(f262,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f164,f143])).

fof(f143,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f73,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f55])).

fof(f55,plain,
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

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
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

fof(f164,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f146,f72])).

fof(f72,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f146,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f73,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f199,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f198,f175])).

fof(f175,plain,(
    sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f159,f170])).

fof(f170,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f74,f71,f144,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f144,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f73,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f74,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f159,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f154,f144])).

fof(f154,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f139,f153])).

fof(f153,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f142,f75])).

fof(f75,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f142,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f73,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f139,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f71])).

fof(f136,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f198,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f197,f174])).

fof(f174,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f172,f170])).

fof(f172,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f74,f71,f144,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f197,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) ),
    inference(subsumption_resolution,[],[f187,f180])).

fof(f180,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f168,f170])).

fof(f168,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f71,f144,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f187,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f179,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f267,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f196,f262])).

fof(f196,plain,(
    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f195,f175])).

fof(f195,plain,(
    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f194,f174])).

fof(f194,plain,(
    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f186,f180])).

fof(f186,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f179,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f179,plain,(
    v1_funct_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f169,f170])).

fof(f169,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f71,f144,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f178,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f177,f170])).

fof(f177,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f176,f170])).

fof(f176,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f76,f170])).

fof(f76,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f283,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f276,f163])).

fof(f163,plain,(
    ! [X0] :
      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f158,f144])).

fof(f158,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(backward_demodulation,[],[f132,f153])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f71,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f276,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f162,f129])).

fof(f129,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f162,plain,(
    ! [X1] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1)))
      | ~ r1_tarski(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f157,f144])).

fof(f157,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(backward_demodulation,[],[f133,f153])).

fof(f133,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK2),X1)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f71,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f519,plain,(
    ~ r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f389,f327])).

fof(f327,plain,(
    ! [X0] :
      ( v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0)
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(backward_demodulation,[],[f190,f313])).

fof(f190,plain,(
    ! [X0] :
      ( v1_funct_2(k4_relat_1(sK2),sK1,X0)
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(forward_demodulation,[],[f189,f175])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),X0) ) ),
    inference(forward_demodulation,[],[f188,f174])).

fof(f188,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0)
      | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f184,f180])).

fof(f184,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0)
      | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),X0)
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(resolution,[],[f179,f104])).

fof(f389,plain,(
    ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(unit_resulting_resolution,[],[f362,f360])).

fof(f360,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f359,f313])).

fof(f359,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f358,f126])).

fof(f126,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f358,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f326,f179])).

fof(f326,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f178,f313])).

fof(f362,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f330,f126])).

fof(f330,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f199,f313])).

fof(f640,plain,(
    ! [X0] : v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f639,f79])).

fof(f639,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f567,f77])).

fof(f77,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f567,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0) ) ),
    inference(backward_demodulation,[],[f327,f523])).

fof(f647,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f580,f523])).

fof(f580,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f360,f523])).

fof(f651,plain,(
    m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f650,f523])).

fof(f650,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f649,f79])).

fof(f649,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f581,f77])).

fof(f581,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X1)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f361,f523])).

fof(f361,plain,(
    ! [X1] :
      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(forward_demodulation,[],[f328,f126])).

fof(f328,plain,(
    ! [X1] :
      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(backward_demodulation,[],[f193,f313])).

fof(f193,plain,(
    ! [X1] :
      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(forward_demodulation,[],[f192,f175])).

fof(f192,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X1))) ) ),
    inference(forward_demodulation,[],[f191,f174])).

fof(f191,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X1))) ) ),
    inference(subsumption_resolution,[],[f185,f180])).

fof(f185,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X1)))
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(resolution,[],[f179,f105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (12144)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (12142)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (12144)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f652,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f651,f648])).
% 0.20/0.46  fof(f648,plain,(
% 0.20/0.46    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.46    inference(subsumption_resolution,[],[f647,f641])).
% 0.20/0.46  fof(f641,plain,(
% 0.20/0.46    ( ! [X0] : (v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,X0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f640,f523])).
% 0.20/0.46  fof(f523,plain,(
% 0.20/0.46    k1_xboole_0 = sK2),
% 0.20/0.46    inference(subsumption_resolution,[],[f522,f79])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.46  fof(f522,plain,(
% 0.20/0.46    ~r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 = sK2),
% 0.20/0.46    inference(superposition,[],[f519,f377])).
% 0.20/0.46  fof(f377,plain,(
% 0.20/0.46    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.20/0.46    inference(subsumption_resolution,[],[f344,f79])).
% 0.20/0.46  fof(f344,plain,(
% 0.20/0.46    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.20/0.46    inference(backward_demodulation,[],[f283,f313])).
% 0.20/0.46  fof(f313,plain,(
% 0.20/0.46    k1_xboole_0 = sK1),
% 0.20/0.46    inference(global_subsumption,[],[f178,f179,f267,f308])).
% 0.20/0.46  fof(f308,plain,(
% 0.20/0.46    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK1),
% 0.20/0.46    inference(superposition,[],[f199,f262])).
% 0.20/0.46  fof(f262,plain,(
% 0.20/0.46    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.20/0.46    inference(superposition,[],[f164,f143])).
% 0.20/0.46  fof(f143,plain,(
% 0.20/0.46    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f73,f114])).
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.46    inference(cnf_transformation,[],[f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.46    inference(flattening,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f26])).
% 0.20/0.46  fof(f26,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f25])).
% 0.20/0.46  fof(f25,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.46  fof(f164,plain,(
% 0.20/0.46    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.20/0.46    inference(subsumption_resolution,[],[f146,f72])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f56])).
% 0.20/0.46  fof(f146,plain,(
% 0.20/0.46    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.46    inference(resolution,[],[f73,f116])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f70])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(nnf_transformation,[],[f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(flattening,[],[f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.46  fof(f199,plain,(
% 0.20/0.46    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.20/0.46    inference(forward_demodulation,[],[f198,f175])).
% 0.20/0.46  fof(f175,plain,(
% 0.20/0.46    sK1 = k1_relat_1(k4_relat_1(sK2))),
% 0.20/0.46    inference(backward_demodulation,[],[f159,f170])).
% 0.20/0.46  fof(f170,plain,(
% 0.20/0.46    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f74,f71,f144,f96])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,axiom,(
% 0.20/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.46  fof(f144,plain,(
% 0.20/0.46    v1_relat_1(sK2)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f73,f113])).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    v1_funct_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f56])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    v2_funct_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f56])).
% 0.20/0.46  fof(f159,plain,(
% 0.20/0.46    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.46    inference(subsumption_resolution,[],[f154,f144])).
% 0.20/0.46  fof(f154,plain,(
% 0.20/0.46    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.46    inference(backward_demodulation,[],[f139,f153])).
% 0.20/0.46  fof(f153,plain,(
% 0.20/0.46    sK1 = k2_relat_1(sK2)),
% 0.20/0.46    inference(forward_demodulation,[],[f142,f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f56])).
% 0.20/0.46  fof(f142,plain,(
% 0.20/0.46    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f73,f115])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.46    inference(subsumption_resolution,[],[f136,f71])).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.46    inference(resolution,[],[f74,f97])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,axiom,(
% 0.20/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.46  fof(f198,plain,(
% 0.20/0.46    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))))),
% 0.20/0.46    inference(forward_demodulation,[],[f197,f174])).
% 0.20/0.46  fof(f174,plain,(
% 0.20/0.46    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.20/0.46    inference(backward_demodulation,[],[f172,f170])).
% 0.20/0.46  fof(f172,plain,(
% 0.20/0.46    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f74,f71,f144,f98])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f44])).
% 0.20/0.46  fof(f197,plain,(
% 0.20/0.46    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))),
% 0.20/0.46    inference(subsumption_resolution,[],[f187,f180])).
% 0.20/0.46  fof(f180,plain,(
% 0.20/0.46    v1_relat_1(k4_relat_1(sK2))),
% 0.20/0.46    inference(forward_demodulation,[],[f168,f170])).
% 0.20/0.46  fof(f168,plain,(
% 0.20/0.46    v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f71,f144,f94])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,axiom,(
% 0.20/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.46  fof(f187,plain,(
% 0.20/0.46    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) | ~v1_relat_1(k4_relat_1(sK2))),
% 0.20/0.46    inference(resolution,[],[f179,f93])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,axiom,(
% 0.20/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.46  fof(f267,plain,(
% 0.20/0.46    v1_funct_2(k4_relat_1(sK2),sK1,sK0) | k1_xboole_0 = sK1),
% 0.20/0.46    inference(superposition,[],[f196,f262])).
% 0.20/0.46  fof(f196,plain,(
% 0.20/0.46    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))),
% 0.20/0.46    inference(forward_demodulation,[],[f195,f175])).
% 0.20/0.46  fof(f195,plain,(
% 0.20/0.46    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))),
% 0.20/0.46    inference(forward_demodulation,[],[f194,f174])).
% 0.20/0.46  fof(f194,plain,(
% 0.20/0.46    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))),
% 0.20/0.46    inference(subsumption_resolution,[],[f186,f180])).
% 0.20/0.46  fof(f186,plain,(
% 0.20/0.46    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) | ~v1_relat_1(k4_relat_1(sK2))),
% 0.20/0.46    inference(resolution,[],[f179,f92])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f38])).
% 0.20/0.46  fof(f179,plain,(
% 0.20/0.46    v1_funct_1(k4_relat_1(sK2))),
% 0.20/0.46    inference(forward_demodulation,[],[f169,f170])).
% 0.20/0.46  fof(f169,plain,(
% 0.20/0.46    v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f71,f144,f95])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f40])).
% 0.20/0.46  fof(f178,plain,(
% 0.20/0.46    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.20/0.46    inference(forward_demodulation,[],[f177,f170])).
% 0.20/0.46  fof(f177,plain,(
% 0.20/0.46    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.46    inference(forward_demodulation,[],[f176,f170])).
% 0.20/0.46  fof(f176,plain,(
% 0.20/0.46    ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.46    inference(backward_demodulation,[],[f76,f170])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f56])).
% 0.20/0.46  fof(f283,plain,(
% 0.20/0.46    ~r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.20/0.46    inference(subsumption_resolution,[],[f276,f163])).
% 0.20/0.46  fof(f163,plain,(
% 0.20/0.46    ( ! [X0] : (v1_funct_2(sK2,k1_relat_1(sK2),X0) | ~r1_tarski(sK1,X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f158,f144])).
% 0.20/0.46  fof(f158,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(sK1,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.46    inference(backward_demodulation,[],[f132,f153])).
% 0.20/0.46  fof(f132,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.46    inference(resolution,[],[f71,f104])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.46  fof(f276,plain,(
% 0.20/0.46    ~r1_tarski(sK1,k1_xboole_0) | ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.20/0.46    inference(resolution,[],[f162,f129])).
% 0.20/0.46  fof(f129,plain,(
% 0.20/0.46    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.20/0.46    inference(equality_resolution,[],[f120])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f70])).
% 0.20/0.46  fof(f162,plain,(
% 0.20/0.46    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1))) | ~r1_tarski(sK1,X1)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f157,f144])).
% 0.20/0.46  fof(f157,plain,(
% 0.20/0.46    ( ! [X1] : (~r1_tarski(sK1,X1) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1))) | ~v1_relat_1(sK2)) )),
% 0.20/0.46    inference(backward_demodulation,[],[f133,f153])).
% 0.20/0.46  fof(f133,plain,(
% 0.20/0.46    ( ! [X1] : (~r1_tarski(k2_relat_1(sK2),X1) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1))) | ~v1_relat_1(sK2)) )),
% 0.20/0.46    inference(resolution,[],[f71,f105])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f47])).
% 0.20/0.46  fof(f519,plain,(
% 0.20/0.46    ~r1_tarski(k1_relat_1(sK2),sK0)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f389,f327])).
% 0.20/0.46  fof(f327,plain,(
% 0.20/0.46    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.20/0.46    inference(backward_demodulation,[],[f190,f313])).
% 0.20/0.46  fof(f190,plain,(
% 0.20/0.46    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),sK1,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f189,f175])).
% 0.20/0.46  fof(f189,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),X0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f188,f174])).
% 0.20/0.46  fof(f188,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f184,f180])).
% 0.20/0.46  fof(f184,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),X0) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.20/0.46    inference(resolution,[],[f179,f104])).
% 0.20/0.46  fof(f389,plain,(
% 0.20/0.46    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f362,f360])).
% 0.20/0.46  fof(f360,plain,(
% 0.20/0.46    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.46    inference(forward_demodulation,[],[f359,f313])).
% 0.20/0.46  fof(f359,plain,(
% 0.20/0.46    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 0.20/0.46    inference(forward_demodulation,[],[f358,f126])).
% 0.20/0.46  fof(f126,plain,(
% 0.20/0.46    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.46    inference(equality_resolution,[],[f111])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f69])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.46    inference(flattening,[],[f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.46  fof(f358,plain,(
% 0.20/0.46    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f326,f179])).
% 0.20/0.46  fof(f326,plain,(
% 0.20/0.46    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.20/0.46    inference(backward_demodulation,[],[f178,f313])).
% 0.20/0.46  fof(f362,plain,(
% 0.20/0.46    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.46    inference(forward_demodulation,[],[f330,f126])).
% 0.20/0.46  fof(f330,plain,(
% 0.20/0.46    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))),
% 0.20/0.46    inference(backward_demodulation,[],[f199,f313])).
% 0.20/0.46  fof(f640,plain,(
% 0.20/0.46    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f639,f79])).
% 0.20/0.46  fof(f639,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f567,f77])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,axiom,(
% 0.20/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.46  fof(f567,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0)) )),
% 0.20/0.46    inference(backward_demodulation,[],[f327,f523])).
% 0.20/0.46  fof(f647,plain,(
% 0.20/0.46    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.46    inference(forward_demodulation,[],[f580,f523])).
% 0.20/0.46  fof(f580,plain,(
% 0.20/0.46    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.20/0.46    inference(backward_demodulation,[],[f360,f523])).
% 0.20/0.46  fof(f651,plain,(
% 0.20/0.46    m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.46    inference(forward_demodulation,[],[f650,f523])).
% 0.20/0.46  fof(f650,plain,(
% 0.20/0.46    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.46    inference(subsumption_resolution,[],[f649,f79])).
% 0.20/0.46  fof(f649,plain,(
% 0.20/0.46    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f581,f77])).
% 0.20/0.46  fof(f581,plain,(
% 0.20/0.46    ( ! [X1] : (~r1_tarski(k1_relat_1(k1_xboole_0),X1) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.46    inference(backward_demodulation,[],[f361,f523])).
% 0.20/0.46  fof(f361,plain,(
% 0.20/0.46    ( ! [X1] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(sK2),X1)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f328,f126])).
% 0.20/0.46  fof(f328,plain,(
% 0.20/0.46    ( ! [X1] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_tarski(k1_relat_1(sK2),X1)) )),
% 0.20/0.46    inference(backward_demodulation,[],[f193,f313])).
% 0.20/0.46  fof(f193,plain,(
% 0.20/0.46    ( ! [X1] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k1_relat_1(sK2),X1)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f192,f175])).
% 0.20/0.46  fof(f192,plain,(
% 0.20/0.46    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X1)))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f191,f174])).
% 0.20/0.46  fof(f191,plain,(
% 0.20/0.46    ( ! [X1] : (~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X1)))) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f185,f180])).
% 0.20/0.46  fof(f185,plain,(
% 0.20/0.46    ( ! [X1] : (~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X1))) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.20/0.46    inference(resolution,[],[f179,f105])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (12144)------------------------------
% 0.20/0.46  % (12144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (12144)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (12144)Memory used [KB]: 6524
% 0.20/0.46  % (12144)Time elapsed: 0.059 s
% 0.20/0.46  % (12144)------------------------------
% 0.20/0.46  % (12144)------------------------------
% 0.20/0.46  % (12128)Success in time 0.109 s
%------------------------------------------------------------------------------
