%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0985+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:01 EST 2020

% Result     : Theorem 22.71s
% Output     : Refutation 22.71s
% Verified   : 
% Statistics : Number of formulae       :  144 (1651 expanded)
%              Number of leaves         :   22 ( 402 expanded)
%              Depth                    :   28
%              Number of atoms          :  391 (9564 expanded)
%              Number of equality atoms :  125 (1565 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12852,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12851,f4427])).

fof(f4427,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f12851,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f12850,f11920])).

fof(f11920,plain,(
    k1_xboole_0 = sK60 ),
    inference(forward_demodulation,[],[f11291,f4438])).

fof(f4438,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f856,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f11291,plain,(
    k2_relat_1(k1_xboole_0) = sK60 ),
    inference(backward_demodulation,[],[f8169,f11216])).

fof(f11216,plain,(
    k1_xboole_0 = sK61 ),
    inference(forward_demodulation,[],[f11215,f4472])).

fof(f4472,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f753])).

fof(f753,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f11215,plain,(
    sK61 = k9_relat_1(k1_xboole_0,sK61) ),
    inference(forward_demodulation,[],[f11214,f4431])).

fof(f4431,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f873])).

fof(f873,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f11214,plain,(
    sK61 = k9_relat_1(k6_relat_1(k1_xboole_0),sK61) ),
    inference(forward_demodulation,[],[f10923,f7421])).

fof(f7421,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f6100])).

fof(f6100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f4000])).

fof(f4000,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f3999])).

fof(f3999,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f10923,plain,(
    sK61 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_xboole_0,sK60)),sK61) ),
    inference(backward_demodulation,[],[f7842,f10903])).

fof(f10903,plain,(
    k1_xboole_0 = sK59 ),
    inference(subsumption_resolution,[],[f10902,f9889])).

fof(f9889,plain,(
    m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59))) ),
    inference(subsumption_resolution,[],[f9888,f4421])).

fof(f4421,plain,(
    m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK59,sK60))) ),
    inference(cnf_transformation,[],[f3171])).

fof(f3171,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59)))
      | ~ v1_funct_2(k2_funct_1(sK61),sK60,sK59)
      | ~ v1_funct_1(k2_funct_1(sK61)) )
    & sK60 = k2_relset_1(sK59,sK60,sK61)
    & v2_funct_1(sK61)
    & m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK59,sK60)))
    & v1_funct_2(sK61,sK59,sK60)
    & v1_funct_1(sK61) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK59,sK60,sK61])],[f1550,f3170])).

fof(f3170,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59)))
        | ~ v1_funct_2(k2_funct_1(sK61),sK60,sK59)
        | ~ v1_funct_1(k2_funct_1(sK61)) )
      & sK60 = k2_relset_1(sK59,sK60,sK61)
      & v2_funct_1(sK61)
      & m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK59,sK60)))
      & v1_funct_2(sK61,sK59,sK60)
      & v1_funct_1(sK61) ) ),
    introduced(choice_axiom,[])).

fof(f1550,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1549])).

fof(f1549,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1506])).

fof(f1506,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1505])).

fof(f1505,conjecture,(
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

fof(f9888,plain,
    ( m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59)))
    | ~ m1_subset_1(sK61,k1_zfmisc_1(k2_zfmisc_1(sK59,sK60))) ),
    inference(superposition,[],[f6373,f7819])).

fof(f7819,plain,(
    k4_relat_1(sK61) = k3_relset_1(sK59,sK60,sK61) ),
    inference(resolution,[],[f4421,f6369])).

fof(f6369,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2666])).

fof(f2666,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1229])).

fof(f1229,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f6373,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2670])).

fof(f2670,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1217])).

fof(f1217,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f10902,plain,
    ( k1_xboole_0 = sK59
    | ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59))) ),
    inference(subsumption_resolution,[],[f10899,f9891])).

fof(f9891,plain,(
    ~ v1_funct_2(k4_relat_1(sK61),sK60,sK59) ),
    inference(subsumption_resolution,[],[f8835,f9889])).

fof(f8835,plain,
    ( ~ v1_funct_2(k4_relat_1(sK61),sK60,sK59)
    | ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59))) ),
    inference(subsumption_resolution,[],[f8167,f8831])).

fof(f8831,plain,(
    v1_funct_1(k4_relat_1(sK61)) ),
    inference(subsumption_resolution,[],[f8830,f7816])).

fof(f7816,plain,(
    v1_relat_1(sK61) ),
    inference(resolution,[],[f4421,f6365])).

fof(f6365,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2662])).

fof(f2662,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f8830,plain,
    ( v1_funct_1(k4_relat_1(sK61))
    | ~ v1_relat_1(sK61) ),
    inference(subsumption_resolution,[],[f8823,f4419])).

fof(f4419,plain,(
    v1_funct_1(sK61) ),
    inference(cnf_transformation,[],[f3171])).

fof(f8823,plain,
    ( v1_funct_1(k4_relat_1(sK61))
    | ~ v1_funct_1(sK61)
    | ~ v1_relat_1(sK61) ),
    inference(superposition,[],[f4983,f7906])).

fof(f7906,plain,(
    k2_funct_1(sK61) = k4_relat_1(sK61) ),
    inference(subsumption_resolution,[],[f7665,f7816])).

fof(f7665,plain,
    ( k2_funct_1(sK61) = k4_relat_1(sK61)
    | ~ v1_relat_1(sK61) ),
    inference(subsumption_resolution,[],[f7648,f4419])).

fof(f7648,plain,
    ( k2_funct_1(sK61) = k4_relat_1(sK61)
    | ~ v1_funct_1(sK61)
    | ~ v1_relat_1(sK61) ),
    inference(resolution,[],[f4422,f4985])).

fof(f4985,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1867])).

fof(f1867,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1866])).

fof(f1866,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f906])).

fof(f906,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f4422,plain,(
    v2_funct_1(sK61) ),
    inference(cnf_transformation,[],[f3171])).

fof(f4983,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1863])).

fof(f1863,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1862])).

fof(f1862,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f908])).

fof(f908,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f8167,plain,
    ( ~ v1_funct_2(k4_relat_1(sK61),sK60,sK59)
    | ~ v1_funct_1(k4_relat_1(sK61))
    | ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59))) ),
    inference(forward_demodulation,[],[f8166,f7906])).

fof(f8166,plain,
    ( ~ v1_funct_2(k4_relat_1(sK61),sK60,sK59)
    | ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59)))
    | ~ v1_funct_1(k2_funct_1(sK61)) ),
    inference(forward_demodulation,[],[f8072,f7906])).

fof(f8072,plain,
    ( ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59)))
    | ~ v1_funct_2(k2_funct_1(sK61),sK60,sK59)
    | ~ v1_funct_1(k2_funct_1(sK61)) ),
    inference(backward_demodulation,[],[f4424,f7906])).

fof(f4424,plain,
    ( ~ m1_subset_1(k2_funct_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59)))
    | ~ v1_funct_2(k2_funct_1(sK61),sK60,sK59)
    | ~ v1_funct_1(k2_funct_1(sK61)) ),
    inference(cnf_transformation,[],[f3171])).

fof(f10899,plain,
    ( v1_funct_2(k4_relat_1(sK61),sK60,sK59)
    | k1_xboole_0 = sK59
    | ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59))) ),
    inference(trivial_inequality_removal,[],[f10894])).

fof(f10894,plain,
    ( sK60 != sK60
    | v1_funct_2(k4_relat_1(sK61),sK60,sK59)
    | k1_xboole_0 = sK59
    | ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59))) ),
    inference(superposition,[],[f6386,f8195])).

fof(f8195,plain,(
    sK60 = k1_relset_1(sK60,sK59,k4_relat_1(sK61)) ),
    inference(forward_demodulation,[],[f8194,f4423])).

fof(f4423,plain,(
    sK60 = k2_relset_1(sK59,sK60,sK61) ),
    inference(cnf_transformation,[],[f3171])).

fof(f8194,plain,(
    k2_relset_1(sK59,sK60,sK61) = k1_relset_1(sK60,sK59,k4_relat_1(sK61)) ),
    inference(forward_demodulation,[],[f7823,f7819])).

fof(f7823,plain,(
    k2_relset_1(sK59,sK60,sK61) = k1_relset_1(sK60,sK59,k3_relset_1(sK59,sK60,sK61)) ),
    inference(resolution,[],[f4421,f6378])).

fof(f6378,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f2673])).

fof(f2673,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1247])).

fof(f1247,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

fof(f6386,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f4062])).

fof(f4062,plain,(
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
    inference(nnf_transformation,[],[f2677])).

fof(f2677,plain,(
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
    inference(flattening,[],[f2676])).

fof(f2676,plain,(
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
    inference(ennf_transformation,[],[f1472])).

fof(f1472,axiom,(
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

fof(f7842,plain,(
    sK61 = k9_relat_1(k6_relat_1(k2_zfmisc_1(sK59,sK60)),sK61) ),
    inference(resolution,[],[f4421,f5689])).

fof(f5689,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f2236])).

fof(f2236,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f983])).

fof(f983,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f8169,plain,(
    sK60 = k2_relat_1(sK61) ),
    inference(forward_demodulation,[],[f7817,f4423])).

fof(f7817,plain,(
    k2_relset_1(sK59,sK60,sK61) = k2_relat_1(sK61) ),
    inference(resolution,[],[f4421,f6367])).

fof(f6367,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2664])).

fof(f2664,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f12850,plain,(
    ~ v1_xboole_0(sK60) ),
    inference(subsumption_resolution,[],[f12849,f12474])).

fof(f12474,plain,(
    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f12473,f4429])).

fof(f4429,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f861])).

fof(f861,axiom,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

fof(f12473,plain,(
    m1_subset_1(k4_relat_1(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f12472,f4434])).

fof(f4434,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f12472,plain,(
    m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f12471,f7420])).

fof(f7420,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f6101])).

fof(f6101,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f4000])).

fof(f12471,plain,(
    m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK60,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f11507,f4437])).

fof(f4437,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f11507,plain,(
    m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK60,k1_relat_1(k1_xboole_0)))) ),
    inference(backward_demodulation,[],[f9110,f11216])).

fof(f9110,plain,(
    m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,k1_relat_1(sK61)))) ),
    inference(forward_demodulation,[],[f9109,f8075])).

fof(f8075,plain,(
    k1_relat_1(sK61) = k2_relat_1(k4_relat_1(sK61)) ),
    inference(backward_demodulation,[],[f7909,f7906])).

fof(f7909,plain,(
    k1_relat_1(sK61) = k2_relat_1(k2_funct_1(sK61)) ),
    inference(subsumption_resolution,[],[f7668,f7816])).

fof(f7668,plain,
    ( k1_relat_1(sK61) = k2_relat_1(k2_funct_1(sK61))
    | ~ v1_relat_1(sK61) ),
    inference(subsumption_resolution,[],[f7651,f4419])).

fof(f7651,plain,
    ( k1_relat_1(sK61) = k2_relat_1(k2_funct_1(sK61))
    | ~ v1_funct_1(sK61)
    | ~ v1_relat_1(sK61) ),
    inference(resolution,[],[f4422,f4988])).

fof(f4988,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1871])).

fof(f1871,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1870])).

fof(f1870,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1026])).

fof(f1026,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f9109,plain,(
    m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,k2_relat_1(k4_relat_1(sK61))))) ),
    inference(subsumption_resolution,[],[f9108,f8168])).

fof(f8168,plain,(
    v1_relat_1(k4_relat_1(sK61)) ),
    inference(forward_demodulation,[],[f7895,f7906])).

fof(f7895,plain,(
    v1_relat_1(k2_funct_1(sK61)) ),
    inference(subsumption_resolution,[],[f7631,f7816])).

fof(f7631,plain,
    ( v1_relat_1(k2_funct_1(sK61))
    | ~ v1_relat_1(sK61) ),
    inference(resolution,[],[f4419,f4982])).

fof(f4982,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1863])).

fof(f9108,plain,
    ( m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,k2_relat_1(k4_relat_1(sK61)))))
    | ~ v1_relat_1(k4_relat_1(sK61)) ),
    inference(subsumption_resolution,[],[f9009,f8831])).

fof(f9009,plain,
    ( m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,k2_relat_1(k4_relat_1(sK61)))))
    | ~ v1_funct_1(k4_relat_1(sK61))
    | ~ v1_relat_1(k4_relat_1(sK61)) ),
    inference(superposition,[],[f4981,f8171])).

fof(f8171,plain,(
    sK60 = k1_relat_1(k4_relat_1(sK61)) ),
    inference(backward_demodulation,[],[f8074,f8169])).

fof(f8074,plain,(
    k2_relat_1(sK61) = k1_relat_1(k4_relat_1(sK61)) ),
    inference(backward_demodulation,[],[f7908,f7906])).

fof(f7908,plain,(
    k2_relat_1(sK61) = k1_relat_1(k2_funct_1(sK61)) ),
    inference(subsumption_resolution,[],[f7667,f7816])).

fof(f7667,plain,
    ( k2_relat_1(sK61) = k1_relat_1(k2_funct_1(sK61))
    | ~ v1_relat_1(sK61) ),
    inference(subsumption_resolution,[],[f7650,f4419])).

fof(f7650,plain,
    ( k2_relat_1(sK61) = k1_relat_1(k2_funct_1(sK61))
    | ~ v1_funct_1(sK61)
    | ~ v1_relat_1(sK61) ),
    inference(resolution,[],[f4422,f4987])).

fof(f4987,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1871])).

fof(f4981,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1861])).

fof(f1861,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1860])).

fof(f1860,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1507])).

fof(f1507,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f12849,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ v1_xboole_0(sK60) ),
    inference(forward_demodulation,[],[f12848,f4429])).

fof(f12848,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ v1_xboole_0(sK60) ),
    inference(forward_demodulation,[],[f12847,f4434])).

fof(f12847,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(sK60) ),
    inference(forward_demodulation,[],[f12846,f7421])).

fof(f12846,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ v1_xboole_0(sK60) ) ),
    inference(forward_demodulation,[],[f11649,f11920])).

fof(f11649,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK60,X0)))
      | ~ v1_xboole_0(sK60) ) ),
    inference(backward_demodulation,[],[f9892,f11216])).

fof(f9892,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,X0)))
      | ~ v1_xboole_0(sK60) ) ),
    inference(resolution,[],[f9890,f5485])).

fof(f5485,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2025])).

fof(f2025,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1469])).

fof(f1469,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f9890,plain,(
    ~ v1_partfun1(k4_relat_1(sK61),sK60) ),
    inference(subsumption_resolution,[],[f8832,f9889])).

fof(f8832,plain,
    ( ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59)))
    | ~ v1_partfun1(k4_relat_1(sK61),sK60) ),
    inference(subsumption_resolution,[],[f8724,f8831])).

fof(f8724,plain,
    ( ~ v1_funct_1(k4_relat_1(sK61))
    | ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59)))
    | ~ v1_partfun1(k4_relat_1(sK61),sK60) ),
    inference(duplicate_literal_removal,[],[f8723])).

fof(f8723,plain,
    ( ~ v1_funct_1(k4_relat_1(sK61))
    | ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59)))
    | ~ v1_partfun1(k4_relat_1(sK61),sK60)
    | ~ v1_funct_1(k4_relat_1(sK61))
    | ~ m1_subset_1(k4_relat_1(sK61),k1_zfmisc_1(k2_zfmisc_1(sK60,sK59))) ),
    inference(resolution,[],[f8167,f6395])).

fof(f6395,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2683])).

fof(f2683,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f2682])).

fof(f2682,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1468])).

fof(f1468,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
%------------------------------------------------------------------------------
