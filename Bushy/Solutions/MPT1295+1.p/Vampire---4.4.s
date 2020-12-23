%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t11_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:35 EDT 2019

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   46 (  80 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   14
%              Number of atoms          :  101 ( 201 expanded)
%              Number of equality atoms :   52 ( 116 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1452,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1451,f232])).

fof(f232,plain,(
    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f152,f64])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k5_setfam_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f60])).

fof(f60,plain,
    ( ? [X0,X1] :
        ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k5_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k5_setfam_1(sK0,sK1))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k5_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k5_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t11_tops_2.p',t11_tops_2)).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f82,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t11_tops_2.p',redefinition_k5_setfam_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t11_tops_2.p',dt_k5_setfam_1)).

fof(f1451,plain,(
    ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f1449])).

fof(f1449,plain,
    ( k3_subset_1(sK0,k3_tarski(sK1)) != k3_subset_1(sK0,k3_tarski(sK1))
    | ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f1447,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t11_tops_2.p',d5_subset_1)).

fof(f1447,plain,(
    k3_subset_1(sK0,k3_tarski(sK1)) != k4_xboole_0(sK0,k3_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f1446,f64])).

fof(f1446,plain,
    ( k3_subset_1(sK0,k3_tarski(sK1)) != k4_xboole_0(sK0,k3_tarski(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f1429,f65])).

fof(f65,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f61])).

fof(f1429,plain,
    ( k3_subset_1(sK0,k3_tarski(sK1)) != k4_xboole_0(sK0,k3_tarski(sK1))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f142,f357])).

fof(f357,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k4_xboole_0(X0,k3_tarski(X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(subsumption_resolution,[],[f351,f92])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f70,f67])).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tops_2__t11_tops_2.p',d4_subset_1)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t11_tops_2.p',dt_k2_subset_1)).

fof(f351,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k4_xboole_0(X0,k3_tarski(X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f171,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t11_tops_2.p',redefinition_k7_subset_1)).

fof(f171,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k3_tarski(X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k3_tarski(X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f93,f79])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(forward_demodulation,[],[f85,f67])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t11_tops_2.p',t47_setfam_1)).

fof(f142,plain,(
    k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k3_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f141,f64])).

fof(f141,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k3_tarski(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f66,f79])).

fof(f66,plain,(
    k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k5_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
