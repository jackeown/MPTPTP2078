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
% DateTime   : Thu Dec  3 13:02:05 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  153 (11464 expanded)
%              Number of leaves         :   16 (2202 expanded)
%              Depth                    :   33
%              Number of atoms          :  398 (53603 expanded)
%              Number of equality atoms :  105 (9279 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f601,plain,(
    $false ),
    inference(subsumption_resolution,[],[f600,f494])).

fof(f494,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f478,f483])).

fof(f483,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f482,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f482,plain,(
    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f481,f425])).

fof(f425,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f424,f97])).

fof(f97,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f424,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f423,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f423,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f422,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f422,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f421,f385])).

fof(f385,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f310,f369])).

fof(f369,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f368,f181])).

fof(f181,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f69,f42])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f368,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f362,f41])).

fof(f41,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f362,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f76,f42])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f310,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f309,f218])).

fof(f218,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f162,f213])).

fof(f213,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f208,f44])).

fof(f44,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f208,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f70,f42])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f162,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f161,f97])).

fof(f161,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f160,f40])).

fof(f160,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f50,f43])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f309,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f308,f166])).

fof(f166,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f165,f97])).

fof(f165,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f164,f40])).

fof(f164,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f51,f43])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f308,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    inference(subsumption_resolution,[],[f306,f97])).

fof(f306,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f154,f40])).

fof(f154,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f152,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f152,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(X0))
      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f47,f49])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f421,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(duplicate_literal_removal,[],[f420])).

fof(f420,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f399,f39])).

fof(f39,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f399,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f373,f314])).

fof(f314,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f310,f68])).

fof(f373,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f219,f369])).

fof(f219,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f167,f213])).

fof(f167,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f163,f166])).

fof(f163,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f46,f162])).

fof(f46,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f481,plain,(
    sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f480,f143])).

fof(f143,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f142,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f140,f45])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f140,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_xboole_0(X7)
      | r1_tarski(X6,X8)
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f120,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f120,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(X2,X3),X4)
      | ~ r1_tarski(X2,X4)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f60,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f480,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f431,f80])).

fof(f431,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f113,f425])).

fof(f113,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f59,f92])).

fof(f92,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f64,f42])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f478,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f428,f80])).

fof(f428,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f42,f425])).

fof(f600,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f599,f587])).

fof(f587,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f586,f80])).

fof(f586,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f585,f498])).

fof(f498,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f192,f497])).

fof(f497,plain,(
    ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f496,f483])).

fof(f496,plain,(
    ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK2) ),
    inference(subsumption_resolution,[],[f488,f143])).

fof(f488,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK2) ) ),
    inference(backward_demodulation,[],[f299,f483])).

% (11703)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f299,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k1_xboole_0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK2) ) ),
    inference(resolution,[],[f291,f40])).

fof(f291,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f289,f227])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,k1_xboole_0,X0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,X1)
      | ~ r1_tarski(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f87,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f82,f81])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f289,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X0,k1_xboole_0,X1)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f288,f63])).

fof(f288,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_xboole_0,X1) ) ),
    inference(subsumption_resolution,[],[f287,f64])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_xboole_0,X1)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f286,f81])).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X0,k1_xboole_0,X1)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f77,f133])).

fof(f133,plain,(
    ! [X0] :
      ( v1_partfun1(X0,k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f132,f63])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_partfun1(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f131,f81])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f56,f45])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

% (11702)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f192,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(resolution,[],[f191,f78])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1) ) ),
    inference(resolution,[],[f185,f63])).

fof(f185,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3) ) ),
    inference(superposition,[],[f69,f81])).

fof(f585,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f584,f483])).

fof(f584,plain,(
    k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f583,f143])).

fof(f583,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f582,f81])).

fof(f582,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f464,f483])).

fof(f464,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f323,f425])).

fof(f323,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f315,f59])).

fof(f315,plain,(
    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) ),
    inference(resolution,[],[f310,f64])).

fof(f599,plain,(
    ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f590,f484])).

fof(f484,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f40,f483])).

fof(f590,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f505,f587])).

fof(f505,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f493,f483])).

fof(f493,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f477,f483])).

fof(f477,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f476,f288])).

fof(f476,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f475,f81])).

fof(f475,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f426,f425])).

fof(f426,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f39,f425])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:55:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.27/0.55  % (11698)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.56  % (11714)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.55/0.58  % (11715)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.55/0.58  % (11706)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.55/0.58  % (11707)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.55/0.59  % (11714)Refutation not found, incomplete strategy% (11714)------------------------------
% 1.55/0.59  % (11714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (11699)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.55/0.59  % (11697)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.55/0.60  % (11698)Refutation found. Thanks to Tanya!
% 1.55/0.60  % SZS status Theorem for theBenchmark
% 1.55/0.60  % (11714)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.60  
% 1.55/0.60  % (11714)Memory used [KB]: 10874
% 1.55/0.60  % (11714)Time elapsed: 0.160 s
% 1.55/0.60  % (11714)------------------------------
% 1.55/0.60  % (11714)------------------------------
% 1.55/0.60  % (11692)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.55/0.60  % SZS output start Proof for theBenchmark
% 1.55/0.60  fof(f601,plain,(
% 1.55/0.60    $false),
% 1.55/0.60    inference(subsumption_resolution,[],[f600,f494])).
% 1.55/0.60  fof(f494,plain,(
% 1.55/0.60    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.55/0.60    inference(backward_demodulation,[],[f478,f483])).
% 1.55/0.60  fof(f483,plain,(
% 1.55/0.60    k1_xboole_0 = sK2),
% 1.55/0.60    inference(forward_demodulation,[],[f482,f80])).
% 1.55/0.60  fof(f80,plain,(
% 1.55/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.55/0.60    inference(equality_resolution,[],[f67])).
% 1.55/0.60  fof(f67,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f5])).
% 1.55/0.60  fof(f5,axiom,(
% 1.55/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.55/0.60  fof(f482,plain,(
% 1.55/0.60    sK2 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 1.55/0.60    inference(forward_demodulation,[],[f481,f425])).
% 1.55/0.60  fof(f425,plain,(
% 1.55/0.60    k1_xboole_0 = sK1),
% 1.55/0.60    inference(subsumption_resolution,[],[f424,f97])).
% 1.55/0.60  fof(f97,plain,(
% 1.55/0.60    v1_relat_1(sK2)),
% 1.55/0.60    inference(resolution,[],[f68,f42])).
% 1.55/0.60  fof(f42,plain,(
% 1.55/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.55/0.60    inference(cnf_transformation,[],[f21])).
% 1.55/0.60  fof(f21,plain,(
% 1.55/0.60    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.55/0.60    inference(flattening,[],[f20])).
% 1.55/0.60  fof(f20,plain,(
% 1.55/0.60    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.55/0.60    inference(ennf_transformation,[],[f19])).
% 1.55/0.60  fof(f19,negated_conjecture,(
% 1.55/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.55/0.60    inference(negated_conjecture,[],[f18])).
% 1.55/0.60  fof(f18,conjecture,(
% 1.55/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.55/0.60  fof(f68,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f32])).
% 1.55/0.60  fof(f32,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.60    inference(ennf_transformation,[],[f9])).
% 1.55/0.60  fof(f9,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.55/0.60  fof(f424,plain,(
% 1.55/0.60    k1_xboole_0 = sK1 | ~v1_relat_1(sK2)),
% 1.55/0.60    inference(subsumption_resolution,[],[f423,f40])).
% 1.55/0.60  fof(f40,plain,(
% 1.55/0.60    v1_funct_1(sK2)),
% 1.55/0.60    inference(cnf_transformation,[],[f21])).
% 1.55/0.60  fof(f423,plain,(
% 1.55/0.60    k1_xboole_0 = sK1 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.55/0.60    inference(resolution,[],[f422,f49])).
% 1.55/0.60  fof(f49,plain,(
% 1.55/0.60    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f25])).
% 1.55/0.60  fof(f25,plain,(
% 1.55/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.60    inference(flattening,[],[f24])).
% 1.55/0.60  fof(f24,plain,(
% 1.55/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f7])).
% 1.55/0.60  fof(f7,axiom,(
% 1.55/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.55/0.60  fof(f422,plain,(
% 1.55/0.60    ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = sK1),
% 1.55/0.60    inference(subsumption_resolution,[],[f421,f385])).
% 1.55/0.60  fof(f385,plain,(
% 1.55/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK1),
% 1.55/0.60    inference(superposition,[],[f310,f369])).
% 1.55/0.60  fof(f369,plain,(
% 1.55/0.60    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.55/0.60    inference(superposition,[],[f368,f181])).
% 1.55/0.60  fof(f181,plain,(
% 1.55/0.60    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.55/0.60    inference(resolution,[],[f69,f42])).
% 1.55/0.60  fof(f69,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f33])).
% 1.55/0.60  fof(f33,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.60    inference(ennf_transformation,[],[f12])).
% 1.55/0.60  fof(f12,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.55/0.60  fof(f368,plain,(
% 1.55/0.60    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 1.55/0.60    inference(subsumption_resolution,[],[f362,f41])).
% 1.55/0.60  fof(f41,plain,(
% 1.55/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.55/0.60    inference(cnf_transformation,[],[f21])).
% 1.55/0.60  fof(f362,plain,(
% 1.55/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.55/0.60    inference(resolution,[],[f76,f42])).
% 1.55/0.60  fof(f76,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f36])).
% 1.55/0.60  fof(f36,plain,(
% 1.55/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.60    inference(flattening,[],[f35])).
% 1.55/0.60  fof(f35,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.60    inference(ennf_transformation,[],[f16])).
% 1.55/0.60  fof(f16,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.55/0.60  fof(f310,plain,(
% 1.55/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 1.55/0.60    inference(forward_demodulation,[],[f309,f218])).
% 1.55/0.60  fof(f218,plain,(
% 1.55/0.60    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 1.55/0.60    inference(backward_demodulation,[],[f162,f213])).
% 1.55/0.60  fof(f213,plain,(
% 1.55/0.60    sK1 = k2_relat_1(sK2)),
% 1.55/0.60    inference(forward_demodulation,[],[f208,f44])).
% 1.55/0.60  fof(f44,plain,(
% 1.55/0.60    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.55/0.60    inference(cnf_transformation,[],[f21])).
% 1.55/0.60  fof(f208,plain,(
% 1.55/0.60    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.55/0.60    inference(resolution,[],[f70,f42])).
% 1.55/0.60  fof(f70,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f34])).
% 1.55/0.60  fof(f34,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.60    inference(ennf_transformation,[],[f13])).
% 1.55/0.60  fof(f13,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.55/0.60  fof(f162,plain,(
% 1.55/0.60    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.55/0.60    inference(subsumption_resolution,[],[f161,f97])).
% 1.55/0.60  fof(f161,plain,(
% 1.55/0.60    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.55/0.60    inference(subsumption_resolution,[],[f160,f40])).
% 1.55/0.60  fof(f160,plain,(
% 1.55/0.60    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.55/0.60    inference(resolution,[],[f50,f43])).
% 1.55/0.60  fof(f43,plain,(
% 1.55/0.60    v2_funct_1(sK2)),
% 1.55/0.60    inference(cnf_transformation,[],[f21])).
% 1.55/0.60  fof(f50,plain,(
% 1.55/0.60    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f27])).
% 1.55/0.60  fof(f27,plain,(
% 1.55/0.60    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.60    inference(flattening,[],[f26])).
% 1.55/0.60  fof(f26,plain,(
% 1.55/0.60    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f8])).
% 1.55/0.60  fof(f8,axiom,(
% 1.55/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.55/0.60  fof(f309,plain,(
% 1.55/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))),
% 1.55/0.60    inference(forward_demodulation,[],[f308,f166])).
% 1.55/0.60  fof(f166,plain,(
% 1.55/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.55/0.60    inference(subsumption_resolution,[],[f165,f97])).
% 1.55/0.60  fof(f165,plain,(
% 1.55/0.60    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.55/0.60    inference(subsumption_resolution,[],[f164,f40])).
% 1.55/0.60  fof(f164,plain,(
% 1.55/0.60    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.55/0.60    inference(resolution,[],[f51,f43])).
% 1.55/0.60  fof(f51,plain,(
% 1.55/0.60    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f27])).
% 1.55/0.60  fof(f308,plain,(
% 1.55/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 1.55/0.60    inference(subsumption_resolution,[],[f306,f97])).
% 1.55/0.60  fof(f306,plain,(
% 1.55/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(sK2)),
% 1.55/0.60    inference(resolution,[],[f154,f40])).
% 1.55/0.60  fof(f154,plain,(
% 1.55/0.60    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(X0)) )),
% 1.55/0.60    inference(subsumption_resolution,[],[f152,f48])).
% 1.55/0.60  fof(f48,plain,(
% 1.55/0.60    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f25])).
% 1.55/0.60  fof(f152,plain,(
% 1.55/0.60    ( ! [X0] : (~v1_relat_1(k2_funct_1(X0)) | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.60    inference(resolution,[],[f47,f49])).
% 1.55/0.60  fof(f47,plain,(
% 1.55/0.60    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f23])).
% 1.55/0.60  fof(f23,plain,(
% 1.55/0.60    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.60    inference(flattening,[],[f22])).
% 1.55/0.60  fof(f22,plain,(
% 1.55/0.60    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f17])).
% 1.55/0.60  fof(f17,axiom,(
% 1.55/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.55/0.60  fof(f421,plain,(
% 1.55/0.60    ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.55/0.60    inference(duplicate_literal_removal,[],[f420])).
% 1.55/0.60  fof(f420,plain,(
% 1.55/0.60    ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = sK1 | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.55/0.60    inference(resolution,[],[f399,f39])).
% 1.55/0.60  fof(f39,plain,(
% 1.55/0.60    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.55/0.60    inference(cnf_transformation,[],[f21])).
% 1.55/0.60  fof(f399,plain,(
% 1.55/0.60    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = sK1),
% 1.55/0.60    inference(subsumption_resolution,[],[f373,f314])).
% 1.55/0.60  fof(f314,plain,(
% 1.55/0.60    v1_relat_1(k2_funct_1(sK2))),
% 1.55/0.60    inference(resolution,[],[f310,f68])).
% 1.55/0.60  fof(f373,plain,(
% 1.55/0.60    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = sK1),
% 1.55/0.60    inference(superposition,[],[f219,f369])).
% 1.55/0.60  fof(f219,plain,(
% 1.55/0.60    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.55/0.60    inference(backward_demodulation,[],[f167,f213])).
% 1.55/0.60  fof(f167,plain,(
% 1.55/0.60    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.55/0.60    inference(backward_demodulation,[],[f163,f166])).
% 1.55/0.60  fof(f163,plain,(
% 1.55/0.60    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.55/0.60    inference(superposition,[],[f46,f162])).
% 1.55/0.60  fof(f46,plain,(
% 1.55/0.60    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f23])).
% 1.55/0.60  fof(f481,plain,(
% 1.55/0.60    sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.55/0.60    inference(subsumption_resolution,[],[f480,f143])).
% 1.55/0.60  fof(f143,plain,(
% 1.55/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.55/0.60    inference(resolution,[],[f142,f78])).
% 1.55/0.60  fof(f78,plain,(
% 1.55/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.55/0.60    inference(equality_resolution,[],[f58])).
% 1.55/0.60  fof(f58,plain,(
% 1.55/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.55/0.60    inference(cnf_transformation,[],[f4])).
% 1.55/0.60  fof(f4,axiom,(
% 1.55/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.55/0.60  fof(f142,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,X1)) )),
% 1.55/0.60    inference(resolution,[],[f140,f45])).
% 1.55/0.60  fof(f45,plain,(
% 1.55/0.60    v1_xboole_0(k1_xboole_0)),
% 1.55/0.60    inference(cnf_transformation,[],[f3])).
% 1.55/0.60  fof(f3,axiom,(
% 1.55/0.60    v1_xboole_0(k1_xboole_0)),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.55/0.60  fof(f140,plain,(
% 1.55/0.60    ( ! [X6,X8,X7] : (~v1_xboole_0(X7) | r1_tarski(X6,X8) | ~r1_tarski(X6,X7)) )),
% 1.55/0.60    inference(resolution,[],[f120,f53])).
% 1.55/0.60  fof(f53,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f1])).
% 1.55/0.60  fof(f1,axiom,(
% 1.55/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.55/0.60  fof(f120,plain,(
% 1.55/0.60    ( ! [X4,X2,X3] : (r2_hidden(sK4(X2,X3),X4) | ~r1_tarski(X2,X4) | r1_tarski(X2,X3)) )),
% 1.55/0.60    inference(resolution,[],[f60,f61])).
% 1.55/0.60  fof(f61,plain,(
% 1.55/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f31])).
% 1.55/0.60  fof(f31,plain,(
% 1.55/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f2])).
% 1.55/0.60  fof(f2,axiom,(
% 1.55/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.55/0.60  fof(f60,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f31])).
% 1.55/0.60  fof(f480,plain,(
% 1.55/0.60    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.55/0.60    inference(forward_demodulation,[],[f431,f80])).
% 1.55/0.60  fof(f431,plain,(
% 1.55/0.60    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.55/0.60    inference(backward_demodulation,[],[f113,f425])).
% 1.55/0.60  fof(f113,plain,(
% 1.55/0.60    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.55/0.60    inference(resolution,[],[f59,f92])).
% 1.55/0.60  fof(f92,plain,(
% 1.55/0.60    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.55/0.60    inference(resolution,[],[f64,f42])).
% 1.55/0.60  fof(f64,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f6])).
% 1.55/0.60  fof(f6,axiom,(
% 1.55/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.55/0.60  fof(f59,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.55/0.60    inference(cnf_transformation,[],[f4])).
% 1.55/0.60  fof(f478,plain,(
% 1.55/0.60    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.55/0.60    inference(forward_demodulation,[],[f428,f80])).
% 1.55/0.60  fof(f428,plain,(
% 1.55/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.55/0.60    inference(backward_demodulation,[],[f42,f425])).
% 1.55/0.60  fof(f600,plain,(
% 1.55/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.55/0.60    inference(forward_demodulation,[],[f599,f587])).
% 1.55/0.60  fof(f587,plain,(
% 1.55/0.60    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.55/0.60    inference(forward_demodulation,[],[f586,f80])).
% 1.55/0.61  fof(f586,plain,(
% 1.55/0.61    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_xboole_0)),
% 1.55/0.61    inference(forward_demodulation,[],[f585,f498])).
% 1.55/0.61  fof(f498,plain,(
% 1.55/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.55/0.61    inference(backward_demodulation,[],[f192,f497])).
% 1.55/0.61  fof(f497,plain,(
% 1.55/0.61    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.55/0.61    inference(forward_demodulation,[],[f496,f483])).
% 1.55/0.61  fof(f496,plain,(
% 1.55/0.61    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK2)) )),
% 1.55/0.61    inference(subsumption_resolution,[],[f488,f143])).
% 1.55/0.61  fof(f488,plain,(
% 1.55/0.61    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK2)) )),
% 1.55/0.61    inference(backward_demodulation,[],[f299,f483])).
% 1.55/0.61  % (11703)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.55/0.61  fof(f299,plain,(
% 1.55/0.61    ( ! [X0] : (~r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK2)) )),
% 1.55/0.61    inference(resolution,[],[f291,f40])).
% 1.55/0.61  fof(f291,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~v1_funct_1(X0) | ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0)) )),
% 1.55/0.61    inference(duplicate_literal_removal,[],[f290])).
% 1.55/0.61  fof(f290,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~v1_funct_1(X0) | ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.55/0.61    inference(resolution,[],[f289,f227])).
% 1.55/0.61  fof(f227,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~v1_funct_2(X1,k1_xboole_0,X0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,X1) | ~r1_tarski(X1,k1_xboole_0)) )),
% 1.55/0.61    inference(resolution,[],[f87,f63])).
% 1.55/0.61  fof(f63,plain,(
% 1.55/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f6])).
% 1.55/0.61  fof(f87,plain,(
% 1.55/0.61    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.55/0.61    inference(forward_demodulation,[],[f82,f81])).
% 1.55/0.61  fof(f81,plain,(
% 1.55/0.61    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.55/0.61    inference(equality_resolution,[],[f66])).
% 1.55/0.61  fof(f66,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f5])).
% 1.55/0.61  fof(f82,plain,(
% 1.55/0.61    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.55/0.61    inference(equality_resolution,[],[f74])).
% 1.55/0.61  fof(f74,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f36])).
% 1.55/0.61  fof(f289,plain,(
% 1.55/0.61    ( ! [X0,X1] : (v1_funct_2(X0,k1_xboole_0,X1) | ~v1_funct_1(X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.55/0.61    inference(resolution,[],[f288,f63])).
% 1.55/0.61  fof(f288,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_xboole_0,X1)) )),
% 1.55/0.61    inference(subsumption_resolution,[],[f287,f64])).
% 1.55/0.61  fof(f287,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_xboole_0,X1) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.55/0.61    inference(forward_demodulation,[],[f286,f81])).
% 1.55/0.61  fof(f286,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X0,k1_xboole_0,X1) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.55/0.61    inference(resolution,[],[f77,f133])).
% 1.55/0.61  fof(f133,plain,(
% 1.55/0.61    ( ! [X0] : (v1_partfun1(X0,k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.55/0.61    inference(resolution,[],[f132,f63])).
% 1.55/0.61  fof(f132,plain,(
% 1.55/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_partfun1(X0,k1_xboole_0)) )),
% 1.55/0.61    inference(forward_demodulation,[],[f131,f81])).
% 1.55/0.61  fof(f131,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X0,k1_xboole_0)) )),
% 1.55/0.61    inference(resolution,[],[f56,f45])).
% 1.55/0.61  fof(f56,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f30])).
% 1.55/0.61  fof(f30,plain,(
% 1.55/0.61    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.55/0.61    inference(ennf_transformation,[],[f15])).
% 1.55/0.61  % (11702)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.55/0.61  fof(f15,axiom,(
% 1.55/0.61    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 1.55/0.61  fof(f77,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f38])).
% 1.55/0.61  fof(f38,plain,(
% 1.55/0.61    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.61    inference(flattening,[],[f37])).
% 1.55/0.61  fof(f37,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.61    inference(ennf_transformation,[],[f14])).
% 1.55/0.61  fof(f14,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.55/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 1.55/0.61  fof(f192,plain,(
% 1.55/0.61    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.55/0.61    inference(resolution,[],[f191,f78])).
% 1.55/0.61  fof(f191,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)) )),
% 1.55/0.61    inference(resolution,[],[f185,f63])).
% 1.55/0.61  fof(f185,plain,(
% 1.55/0.61    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3)) )),
% 1.55/0.61    inference(superposition,[],[f69,f81])).
% 1.55/0.61  fof(f585,plain,(
% 1.55/0.61    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0))),
% 1.55/0.61    inference(forward_demodulation,[],[f584,f483])).
% 1.55/0.61  fof(f584,plain,(
% 1.55/0.61    k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 1.55/0.61    inference(subsumption_resolution,[],[f583,f143])).
% 1.55/0.61  fof(f583,plain,(
% 1.55/0.61    ~r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 1.55/0.61    inference(forward_demodulation,[],[f582,f81])).
% 1.55/0.61  fof(f582,plain,(
% 1.55/0.61    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 1.55/0.61    inference(forward_demodulation,[],[f464,f483])).
% 1.55/0.61  fof(f464,plain,(
% 1.55/0.61    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 1.55/0.61    inference(backward_demodulation,[],[f323,f425])).
% 1.55/0.61  fof(f323,plain,(
% 1.55/0.61    ~r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 1.55/0.61    inference(resolution,[],[f315,f59])).
% 1.55/0.61  fof(f315,plain,(
% 1.55/0.61    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2)))),
% 1.55/0.61    inference(resolution,[],[f310,f64])).
% 1.55/0.61  fof(f599,plain,(
% 1.55/0.61    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.55/0.61    inference(subsumption_resolution,[],[f590,f484])).
% 1.55/0.61  fof(f484,plain,(
% 1.55/0.61    v1_funct_1(k1_xboole_0)),
% 1.55/0.61    inference(backward_demodulation,[],[f40,f483])).
% 1.55/0.61  fof(f590,plain,(
% 1.55/0.61    ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.55/0.61    inference(backward_demodulation,[],[f505,f587])).
% 1.55/0.61  fof(f505,plain,(
% 1.55/0.61    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0))),
% 1.55/0.61    inference(forward_demodulation,[],[f493,f483])).
% 1.55/0.61  fof(f493,plain,(
% 1.55/0.61    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 1.55/0.61    inference(backward_demodulation,[],[f477,f483])).
% 1.55/0.61  fof(f477,plain,(
% 1.55/0.61    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.55/0.61    inference(subsumption_resolution,[],[f476,f288])).
% 1.55/0.61  fof(f476,plain,(
% 1.55/0.61    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.55/0.61    inference(forward_demodulation,[],[f475,f81])).
% 1.55/0.61  fof(f475,plain,(
% 1.55/0.61    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.55/0.61    inference(forward_demodulation,[],[f426,f425])).
% 1.55/0.61  fof(f426,plain,(
% 1.55/0.61    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.55/0.61    inference(backward_demodulation,[],[f39,f425])).
% 1.55/0.61  % SZS output end Proof for theBenchmark
% 1.55/0.61  % (11698)------------------------------
% 1.55/0.61  % (11698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (11698)Termination reason: Refutation
% 1.55/0.61  
% 1.55/0.61  % (11698)Memory used [KB]: 6524
% 1.55/0.61  % (11698)Time elapsed: 0.174 s
% 1.55/0.61  % (11698)------------------------------
% 1.55/0.61  % (11698)------------------------------
% 1.55/0.61  % (11703)Refutation not found, incomplete strategy% (11703)------------------------------
% 1.55/0.61  % (11703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (11703)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (11703)Memory used [KB]: 10618
% 1.55/0.61  % (11703)Time elapsed: 0.173 s
% 1.55/0.61  % (11703)------------------------------
% 1.55/0.61  % (11703)------------------------------
% 1.55/0.61  % (11691)Success in time 0.246 s
%------------------------------------------------------------------------------
