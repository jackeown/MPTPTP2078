%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0417+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 21.90s
% Output     : Refutation 21.90s
% Verified   : 
% Statistics : Number of formulae       :  281 (2297 expanded)
%              Number of leaves         :   50 ( 641 expanded)
%              Depth                    :   29
%              Number of atoms          :  713 (5378 expanded)
%              Number of equality atoms :  285 (2835 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35554,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35553,f8170])).

fof(f8170,plain,(
    k3_tarski(k7_setfam_1(sK0,sK1)) != k4_xboole_0(sK0,k1_setfam_1(sK1)) ),
    inference(subsumption_resolution,[],[f8167,f2294])).

fof(f2294,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f2272,f2293])).

fof(f2293,plain,(
    sK0 = k3_tarski(k2_tarski(sK0,k3_tarski(sK1))) ),
    inference(backward_demodulation,[],[f2233,f2292])).

fof(f2292,plain,(
    sK0 = k4_subset_1(sK0,k3_tarski(sK1),sK0) ),
    inference(forward_demodulation,[],[f2156,f923])).

fof(f923,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f460])).

fof(f460,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f2156,plain,(
    k2_subset_1(sK0) = k4_subset_1(sK0,k3_tarski(sK1),k2_subset_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1580,f921])).

fof(f921,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f626])).

fof(f626,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f504])).

fof(f504,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f1580,plain,(
    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f1361,f1362])).

fof(f1362,plain,(
    k3_tarski(sK1) = k5_setfam_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f904,f925])).

fof(f925,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f628])).

fof(f628,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f567])).

fof(f567,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f904,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f769])).

fof(f769,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,k2_subset_1(sK0),k6_setfam_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f613,f768])).

fof(f768,plain,
    ( ? [X0,X1] :
        ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,k2_subset_1(sK0),k6_setfam_1(sK0,sK1))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f613,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f612])).

fof(f612,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f602])).

fof(f602,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f601])).

fof(f601,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_setfam_1)).

fof(f1361,plain,(
    m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f904,f924])).

fof(f924,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f627])).

fof(f627,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f557])).

fof(f557,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f2233,plain,(
    k3_tarski(k2_tarski(sK0,k3_tarski(sK1))) = k4_subset_1(sK0,k3_tarski(sK1),sK0) ),
    inference(forward_demodulation,[],[f2232,f1248])).

fof(f1248,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f1186,f1156,f1156])).

fof(f1156,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f317])).

fof(f317,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f1186,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2232,plain,(
    k3_tarski(k2_tarski(k3_tarski(sK1),sK0)) = k4_subset_1(sK0,k3_tarski(sK1),sK0) ),
    inference(forward_demodulation,[],[f2211,f923])).

fof(f2211,plain,(
    k4_subset_1(sK0,k3_tarski(sK1),k2_subset_1(sK0)) = k3_tarski(k2_tarski(k3_tarski(sK1),k2_subset_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f922,f1580,f1219])).

fof(f1219,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f1054,f1156])).

fof(f1054,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f686])).

fof(f686,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f685])).

fof(f685,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f491])).

fof(f491,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f922,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f465])).

fof(f465,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f2272,plain,(
    m1_subset_1(k3_tarski(k2_tarski(sK0,k3_tarski(sK1))),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f2271,f2229])).

fof(f2229,plain,(
    k4_subset_1(sK0,sK0,k3_tarski(sK1)) = k3_tarski(k2_tarski(sK0,k3_tarski(sK1))) ),
    inference(forward_demodulation,[],[f2228,f1248])).

fof(f2228,plain,(
    k4_subset_1(sK0,sK0,k3_tarski(sK1)) = k3_tarski(k2_tarski(k3_tarski(sK1),sK0)) ),
    inference(forward_demodulation,[],[f2227,f923])).

fof(f2227,plain,(
    k4_subset_1(sK0,k2_subset_1(sK0),k3_tarski(sK1)) = k3_tarski(k2_tarski(k3_tarski(sK1),k2_subset_1(sK0))) ),
    inference(forward_demodulation,[],[f2215,f1248])).

fof(f2215,plain,(
    k4_subset_1(sK0,k2_subset_1(sK0),k3_tarski(sK1)) = k3_tarski(k2_tarski(k2_subset_1(sK0),k3_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f922,f1580,f1219])).

fof(f2271,plain,(
    m1_subset_1(k4_subset_1(sK0,sK0,k3_tarski(sK1)),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f2171,f923])).

fof(f2171,plain,(
    m1_subset_1(k4_subset_1(sK0,k2_subset_1(sK0),k3_tarski(sK1)),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f922,f1580,f1055])).

fof(f1055,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f688])).

fof(f688,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f687])).

fof(f687,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f467])).

fof(f467,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f8167,plain,
    ( k3_tarski(k7_setfam_1(sK0,sK1)) != k4_xboole_0(sK0,k1_setfam_1(sK1))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f1606,f907])).

fof(f907,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f614])).

fof(f614,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f494])).

fof(f494,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1606,plain,(
    k7_subset_1(sK0,sK0,k1_setfam_1(sK1)) != k3_tarski(k7_setfam_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1603,f1364])).

fof(f1364,plain,(
    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f904,f932])).

fof(f932,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f632])).

fof(f632,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f559])).

fof(f559,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f1603,plain,
    ( k7_subset_1(sK0,sK0,k1_setfam_1(sK1)) != k3_tarski(k7_setfam_1(sK0,sK1))
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f1581,f925])).

fof(f1581,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,sK0,k1_setfam_1(sK1)) ),
    inference(backward_demodulation,[],[f1293,f1360])).

fof(f1360,plain,(
    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(unit_resulting_resolution,[],[f904,f917])).

fof(f917,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f623])).

fof(f623,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f568])).

fof(f568,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f1293,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,sK0,k6_setfam_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f906,f923])).

fof(f906,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,k2_subset_1(sK0),k6_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f769])).

fof(f35553,plain,(
    k3_tarski(k7_setfam_1(sK0,sK1)) = k4_xboole_0(sK0,k1_setfam_1(sK1)) ),
    inference(forward_demodulation,[],[f35552,f2404])).

fof(f2404,plain,(
    k3_subset_1(sK0,k1_setfam_1(sK1)) = k4_xboole_0(sK0,k1_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1582,f1084])).

fof(f1084,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f716])).

fof(f716,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1582,plain,(
    m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f1359,f1360])).

fof(f1359,plain,(
    m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f904,f916])).

fof(f916,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f622])).

fof(f622,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f558])).

fof(f558,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_setfam_1)).

fof(f35552,plain,(
    k3_tarski(k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k1_setfam_1(sK1)) ),
    inference(forward_demodulation,[],[f35551,f4126])).

fof(f4126,plain,(
    k1_setfam_1(sK1) = k7_subset_1(sK0,sK0,k3_tarski(k7_setfam_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f4125,f1360])).

fof(f4125,plain,(
    k6_setfam_1(sK0,sK1) = k7_subset_1(sK0,sK0,k3_tarski(k7_setfam_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f4124,f923])).

fof(f4124,plain,(
    k6_setfam_1(sK0,sK1) = k7_subset_1(sK0,k2_subset_1(sK0),k3_tarski(k7_setfam_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f4123,f3813])).

fof(f3813,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_tarski(k7_setfam_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1364,f925])).

fof(f4123,plain,(
    k6_setfam_1(sK0,sK1) = k7_subset_1(sK0,k2_subset_1(sK0),k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3809,f1365])).

fof(f1365,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f904,f933])).

fof(f933,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f633])).

fof(f633,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f564])).

fof(f564,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f3809,plain,(
    k7_subset_1(sK0,k2_subset_1(sK0),k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f1363,f1364,f915])).

fof(f915,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f621])).

fof(f621,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f620])).

fof(f620,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f600])).

fof(f600,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_setfam_1)).

fof(f1363,plain,(
    k1_xboole_0 != k7_setfam_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f905,f904,f931])).

fof(f931,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k1_xboole_0 != k7_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f631])).

fof(f631,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f630])).

fof(f630,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f905,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f769])).

fof(f35551,plain,(
    k3_tarski(k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k7_subset_1(sK0,sK0,k3_tarski(k7_setfam_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f35550,f35441])).

fof(f35441,plain,(
    k3_tarski(k7_setfam_1(sK0,sK1)) = k4_subset_1(sK0,k1_xboole_0,k3_tarski(k7_setfam_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f35208,f35438])).

fof(f35438,plain,(
    k3_tarski(k7_setfam_1(sK0,sK1)) = k3_tarski(k2_tarski(k1_xboole_0,k3_tarski(k7_setfam_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f35437,f35240])).

fof(f35240,plain,(
    k3_tarski(k7_setfam_1(sK0,sK1)) = k4_subset_1(sK0,k3_tarski(k7_setfam_1(sK0,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f35190,f1201])).

fof(f1201,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f974,f1156])).

fof(f974,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f35190,plain,(
    k4_subset_1(sK0,k3_tarski(k7_setfam_1(sK0,sK1)),k1_xboole_0) = k3_tarski(k2_tarski(k3_tarski(k7_setfam_1(sK0,sK1)),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f977,f4118,f1219])).

fof(f4118,plain,(
    m1_subset_1(k3_tarski(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f3812,f3813])).

fof(f3812,plain,(
    m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1364,f924])).

fof(f977,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f35437,plain,(
    k4_subset_1(sK0,k3_tarski(k7_setfam_1(sK0,sK1)),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,k3_tarski(k7_setfam_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f35033,f35208])).

fof(f35033,plain,(
    k4_subset_1(sK0,k3_tarski(k7_setfam_1(sK0,sK1)),k1_xboole_0) = k4_subset_1(sK0,k1_xboole_0,k3_tarski(k7_setfam_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f977,f4118,f1053])).

fof(f1053,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f684])).

fof(f684,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f683])).

fof(f683,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f451])).

fof(f451,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f35208,plain,(
    k4_subset_1(sK0,k1_xboole_0,k3_tarski(k7_setfam_1(sK0,sK1))) = k3_tarski(k2_tarski(k1_xboole_0,k3_tarski(k7_setfam_1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f977,f4118,f1219])).

fof(f35550,plain,(
    k3_subset_1(sK0,k7_subset_1(sK0,sK0,k3_tarski(k7_setfam_1(sK0,sK1)))) = k4_subset_1(sK0,k1_xboole_0,k3_tarski(k7_setfam_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f35549,f25371])).

fof(f25371,plain,(
    k1_xboole_0 = k3_subset_1(sK0,sK0) ),
    inference(forward_demodulation,[],[f24799,f975])).

fof(f975,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f24799,plain,(
    k1_xboole_0 = k3_subset_1(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f22506,f24611])).

fof(f24611,plain,(
    k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f22491,f24580])).

fof(f24580,plain,(
    k1_zfmisc_1(sK0) = k3_tarski(k2_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f14733,f1243])).

fof(f1243,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(k1_tarski(X0),X1)) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1181,f1156])).

fof(f1181,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f767])).

fof(f767,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f304])).

fof(f304,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f14733,plain,(
    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f14628,f7015])).

fof(f7015,plain,(
    k1_zfmisc_1(sK0) = k3_subset_1(k1_zfmisc_1(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f7014,f1547])).

fof(f1547,plain,(
    k1_zfmisc_1(sK0) = k3_tarski(k2_tarski(sK1,k1_zfmisc_1(sK0))) ),
    inference(backward_demodulation,[],[f1476,f1546])).

fof(f1546,plain,(
    k1_zfmisc_1(sK0) = k4_subset_1(k1_zfmisc_1(sK0),sK1,k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f1387,f923])).

fof(f1387,plain,(
    k2_subset_1(k1_zfmisc_1(sK0)) = k4_subset_1(k1_zfmisc_1(sK0),sK1,k2_subset_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f904,f921])).

fof(f1476,plain,(
    k3_tarski(k2_tarski(sK1,k1_zfmisc_1(sK0))) = k4_subset_1(k1_zfmisc_1(sK0),sK1,k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f1455,f923])).

fof(f1455,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),sK1,k2_subset_1(k1_zfmisc_1(sK0))) = k3_tarski(k2_tarski(sK1,k2_subset_1(k1_zfmisc_1(sK0)))) ),
    inference(unit_resulting_resolution,[],[f922,f904,f1219])).

fof(f7014,plain,(
    k3_subset_1(k1_zfmisc_1(sK0),k1_xboole_0) = k3_tarski(k2_tarski(sK1,k1_zfmisc_1(sK0))) ),
    inference(forward_demodulation,[],[f7013,f3125])).

fof(f3125,plain,(
    k3_subset_1(k1_zfmisc_1(sK0),k1_xboole_0) = k4_subset_1(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),sK1),sK1) ),
    inference(backward_demodulation,[],[f1573,f3123])).

fof(f3123,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f3076,f976])).

fof(f976,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f3076,plain,(
    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f1212,f1535])).

fof(f1535,plain,(
    sK1 = k3_tarski(k2_tarski(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f1534,f1475])).

fof(f1475,plain,(
    sK1 = k4_subset_1(k1_zfmisc_1(sK0),sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1456,f1201])).

fof(f1456,plain,(
    k3_tarski(k2_tarski(sK1,k1_xboole_0)) = k4_subset_1(k1_zfmisc_1(sK0),sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f977,f904,f1219])).

fof(f1534,plain,(
    k3_tarski(k2_tarski(k1_xboole_0,sK1)) = k4_subset_1(k1_zfmisc_1(sK0),sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1404,f1460])).

fof(f1460,plain,(
    k3_tarski(k2_tarski(k1_xboole_0,sK1)) = k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,sK1) ),
    inference(unit_resulting_resolution,[],[f977,f904,f1219])).

fof(f1404,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),sK1,k1_xboole_0) = k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,sK1) ),
    inference(unit_resulting_resolution,[],[f977,f904,f1053])).

fof(f1212,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f1040,f1156])).

fof(f1040,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1573,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),sK1),sK1) = k3_subset_1(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f1562,f1368])).

fof(f1368,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(k1_zfmisc_1(sK0),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f904,f907])).

fof(f1562,plain,(
    k3_subset_1(k1_zfmisc_1(sK0),k7_subset_1(k1_zfmisc_1(sK0),sK1,sK1)) = k4_subset_1(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f1374,f1442])).

fof(f1442,plain,(
    k3_subset_1(k1_zfmisc_1(sK0),sK1) = k4_xboole_0(k1_zfmisc_1(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f904,f1084])).

fof(f1374,plain,(
    k3_subset_1(k1_zfmisc_1(sK0),k7_subset_1(k1_zfmisc_1(sK0),sK1,sK1)) = k4_subset_1(k1_zfmisc_1(sK0),k3_subset_1(k1_zfmisc_1(sK0),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f904,f904,f913])).

fof(f913,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f618])).

fof(f618,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f507])).

fof(f507,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f7013,plain,(
    k3_tarski(k2_tarski(sK1,k1_zfmisc_1(sK0))) = k4_subset_1(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f7012,f1211])).

fof(f1211,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f1039,f1156,f1156])).

fof(f1039,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f7012,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),sK1),sK1) = k3_tarski(k2_tarski(sK1,k4_xboole_0(k1_zfmisc_1(sK0),sK1))) ),
    inference(forward_demodulation,[],[f6974,f1248])).

fof(f6974,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),sK1),sK1) = k3_tarski(k2_tarski(k4_xboole_0(k1_zfmisc_1(sK0),sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f904,f1490,f1219])).

fof(f1490,plain,(
    m1_subset_1(k4_xboole_0(k1_zfmisc_1(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(backward_demodulation,[],[f1443,f1442])).

fof(f1443,plain,(
    m1_subset_1(k3_subset_1(k1_zfmisc_1(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f904,f1085])).

fof(f1085,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f717])).

fof(f717,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f14628,plain,(
    r2_hidden(k1_xboole_0,k3_subset_1(k1_zfmisc_1(sK0),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f1761,f977,f977,f7484,f1086])).

fof(f1086,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f719])).

fof(f719,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f718])).

fof(f718,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f523])).

fof(f523,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

fof(f7484,plain,(
    k1_xboole_0 != k1_zfmisc_1(sK0) ),
    inference(subsumption_resolution,[],[f7483,f978])).

fof(f978,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f7483,plain,
    ( k1_xboole_0 != k1_zfmisc_1(sK0)
    | ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f7475])).

fof(f7475,plain,
    ( k1_xboole_0 != k1_zfmisc_1(sK0)
    | ~ r1_tarski(k1_zfmisc_1(sK0),sK1) ),
    inference(superposition,[],[f7019,f955])).

fof(f955,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f787])).

fof(f787,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f7019,plain,(
    k1_zfmisc_1(sK0) != k4_xboole_0(k1_zfmisc_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f1496,f7015])).

fof(f1496,plain,(
    k3_subset_1(k1_zfmisc_1(sK0),k1_xboole_0) != k4_xboole_0(k1_zfmisc_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f1439,f1442])).

fof(f1439,plain,(
    k3_subset_1(k1_zfmisc_1(sK0),sK1) != k3_subset_1(k1_zfmisc_1(sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f905,f977,f904,f1080])).

fof(f1080,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f710])).

fof(f710,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f709])).

fof(f709,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f536])).

fof(f536,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_subset_1)).

fof(f1761,plain,(
    ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f978,f1329,f1125])).

fof(f1125,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f874])).

fof(f874,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK29(X0,X1),X1)
          & r2_hidden(sK29(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29])],[f872,f873])).

fof(f873,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK29(X0,X1),X1)
        & r2_hidden(sK29(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f872,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f871])).

fof(f871,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f750])).

fof(f750,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1329,plain,(
    ~ r2_hidden(k1_xboole_0,k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f905,f1282])).

fof(f1282,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f1171])).

fof(f1171,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f903])).

fof(f903,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK42(X0,X1) != X0
            | ~ r2_hidden(sK42(X0,X1),X1) )
          & ( sK42(X0,X1) = X0
            | r2_hidden(sK42(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK42])],[f901,f902])).

fof(f902,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK42(X0,X1) != X0
          | ~ r2_hidden(sK42(X0,X1),X1) )
        & ( sK42(X0,X1) = X0
          | r2_hidden(sK42(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f901,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f900])).

fof(f900,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f22491,plain,(
    k1_xboole_0 = k1_setfam_1(k3_tarski(k2_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0)))) ),
    inference(backward_demodulation,[],[f22446,f22376])).

fof(f22376,plain,(
    k1_xboole_0 = k9_subset_1(sK0,k1_xboole_0,k1_setfam_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f977,f977,f16964,f16964,f3381,f1092])).

fof(f1092,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK23(X0,X1,X2,X3),X2)
      | k9_subset_1(X0,X2,X3) = X1
      | r2_hidden(sK23(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f860])).

fof(f860,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k9_subset_1(X0,X2,X3) = X1
              | ( ( ~ r2_hidden(sK23(X0,X1,X2,X3),X3)
                  | ~ r2_hidden(sK23(X0,X1,X2,X3),X2)
                  | ~ r2_hidden(sK23(X0,X1,X2,X3),X1) )
                & ( ( r2_hidden(sK23(X0,X1,X2,X3),X3)
                    & r2_hidden(sK23(X0,X1,X2,X3),X2) )
                  | r2_hidden(sK23(X0,X1,X2,X3),X1) )
                & m1_subset_1(sK23(X0,X1,X2,X3),X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f858,f859])).

fof(f859,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(X4,X3)
            | ~ r2_hidden(X4,X2)
            | ~ r2_hidden(X4,X1) )
          & ( ( r2_hidden(X4,X3)
              & r2_hidden(X4,X2) )
            | r2_hidden(X4,X1) )
          & m1_subset_1(X4,X0) )
     => ( ( ~ r2_hidden(sK23(X0,X1,X2,X3),X3)
          | ~ r2_hidden(sK23(X0,X1,X2,X3),X2)
          | ~ r2_hidden(sK23(X0,X1,X2,X3),X1) )
        & ( ( r2_hidden(sK23(X0,X1,X2,X3),X3)
            & r2_hidden(sK23(X0,X1,X2,X3),X2) )
          | r2_hidden(sK23(X0,X1,X2,X3),X1) )
        & m1_subset_1(sK23(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f858,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k9_subset_1(X0,X2,X3) = X1
              | ? [X4] :
                  ( ( ~ r2_hidden(X4,X3)
                    | ~ r2_hidden(X4,X2)
                    | ~ r2_hidden(X4,X1) )
                  & ( ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) )
                    | r2_hidden(X4,X1) )
                  & m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f857])).

fof(f857,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k9_subset_1(X0,X2,X3) = X1
              | ? [X4] :
                  ( ( ~ r2_hidden(X4,X3)
                    | ~ r2_hidden(X4,X2)
                    | ~ r2_hidden(X4,X1) )
                  & ( ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) )
                    | r2_hidden(X4,X1) )
                  & m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f725])).

fof(f725,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k9_subset_1(X0,X2,X3) = X1
              | ? [X4] :
                  ( ( r2_hidden(X4,X1)
                  <~> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  & m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f724])).

fof(f724,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( k9_subset_1(X0,X2,X3) = X1
              | ? [X4] :
                  ( ( r2_hidden(X4,X1)
                  <~> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  & m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f499])).

fof(f499,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) ) ) )
               => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_subset_1)).

fof(f3381,plain,(
    m1_subset_1(k1_setfam_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f3133,f3134])).

fof(f3134,plain,(
    k1_setfam_1(k1_zfmisc_1(sK0)) = k6_setfam_1(sK0,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1548,f917])).

fof(f1548,plain,(
    m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(backward_demodulation,[],[f1526,f1547])).

fof(f1526,plain,(
    m1_subset_1(k3_tarski(k2_tarski(sK1,k1_zfmisc_1(sK0))),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(forward_demodulation,[],[f1525,f1473])).

fof(f1473,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),sK1) = k3_tarski(k2_tarski(sK1,k1_zfmisc_1(sK0))) ),
    inference(forward_demodulation,[],[f1472,f923])).

fof(f1472,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),k2_subset_1(k1_zfmisc_1(sK0)),sK1) = k3_tarski(k2_tarski(sK1,k2_subset_1(k1_zfmisc_1(sK0)))) ),
    inference(forward_demodulation,[],[f1459,f1248])).

fof(f1459,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),k2_subset_1(k1_zfmisc_1(sK0)),sK1) = k3_tarski(k2_tarski(k2_subset_1(k1_zfmisc_1(sK0)),sK1)) ),
    inference(unit_resulting_resolution,[],[f922,f904,f1219])).

fof(f1525,plain,(
    m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(forward_demodulation,[],[f1411,f923])).

fof(f1411,plain,(
    m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),k2_subset_1(k1_zfmisc_1(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f922,f904,f1055])).

fof(f3133,plain,(
    m1_subset_1(k6_setfam_1(sK0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1548,f916])).

fof(f16964,plain,(
    ! [X12] : ~ r2_hidden(X12,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f16957,f3091])).

fof(f3091,plain,(
    ! [X23] :
      ( r2_hidden(X23,sK1)
      | ~ r2_hidden(X23,k1_xboole_0) ) ),
    inference(superposition,[],[f1265,f1535])).

fof(f1265,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f1217])).

fof(f1217,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f1043,f1156])).

fof(f1043,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f832])).

fof(f832,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK16(X0,X1,X2),X1)
              & ~ r2_hidden(sK16(X0,X1,X2),X0) )
            | ~ r2_hidden(sK16(X0,X1,X2),X2) )
          & ( r2_hidden(sK16(X0,X1,X2),X1)
            | r2_hidden(sK16(X0,X1,X2),X0)
            | r2_hidden(sK16(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f830,f831])).

fof(f831,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK16(X0,X1,X2),X1)
            & ~ r2_hidden(sK16(X0,X1,X2),X0) )
          | ~ r2_hidden(sK16(X0,X1,X2),X2) )
        & ( r2_hidden(sK16(X0,X1,X2),X1)
          | r2_hidden(sK16(X0,X1,X2),X0)
          | r2_hidden(sK16(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f830,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f829])).

fof(f829,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f828])).

fof(f828,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f16957,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,k1_xboole_0)
      | ~ r2_hidden(X12,sK1) ) ),
    inference(superposition,[],[f1261,f3123])).

fof(f1261,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f1012])).

fof(f1012,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f823])).

fof(f823,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK15(X0,X1,X2),X1)
            | ~ r2_hidden(sK15(X0,X1,X2),X0)
            | ~ r2_hidden(sK15(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
              & r2_hidden(sK15(X0,X1,X2),X0) )
            | r2_hidden(sK15(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f821,f822])).

% (30986)Termination reason: Time limit
% (30986)Termination phase: Saturation

% (30986)Memory used [KB]: 22515
% (30986)Time elapsed: 0.811 s
% (30986)------------------------------
% (30986)------------------------------
fof(f822,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK15(X0,X1,X2),X1)
          | ~ r2_hidden(sK15(X0,X1,X2),X0)
          | ~ r2_hidden(sK15(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
            & r2_hidden(sK15(X0,X1,X2),X0) )
          | r2_hidden(sK15(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f821,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f820])).

fof(f820,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f819])).

fof(f819,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f22446,plain,(
    k1_setfam_1(k3_tarski(k2_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0)))) = k9_subset_1(sK0,k1_xboole_0,k1_setfam_1(k1_zfmisc_1(sK0))) ),
    inference(backward_demodulation,[],[f14699,f22430])).

fof(f22430,plain,(
    ! [X0] : k9_subset_1(sK0,X0,k1_setfam_1(k1_zfmisc_1(sK0))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k1_zfmisc_1(sK0)))) ),
    inference(unit_resulting_resolution,[],[f3381,f1220])).

fof(f1220,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f1088,f1111])).

fof(f1111,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f573])).

fof(f573,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f1088,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f721])).

fof(f721,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f14699,plain,(
    k1_setfam_1(k3_tarski(k2_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0)))) = k1_setfam_1(k2_tarski(k1_xboole_0,k1_setfam_1(k1_zfmisc_1(sK0)))) ),
    inference(forward_demodulation,[],[f14650,f1114])).

fof(f1114,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f572])).

fof(f572,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f14650,plain,(
    k1_setfam_1(k3_tarski(k2_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k1_tarski(k1_xboole_0)),k1_setfam_1(k1_zfmisc_1(sK0)))) ),
    inference(unit_resulting_resolution,[],[f3660,f7484,f1221])).

fof(f1221,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f1098,f1156,f1111])).

fof(f1098,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f731])).

fof(f731,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f571])).

fof(f571,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f3660,plain,(
    k1_xboole_0 != k1_tarski(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f3575,f905])).

fof(f3575,plain,
    ( k1_xboole_0 != k1_tarski(k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f1308,f1028])).

fof(f1028,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f824])).

fof(f824,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f377])).

fof(f377,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f1308,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f905,f962])).

fof(f962,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f639])).

fof(f639,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f378])).

fof(f378,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f22506,plain,(
    k1_setfam_1(k1_zfmisc_1(sK0)) = k3_subset_1(sK0,k4_xboole_0(sK0,k1_setfam_1(k1_zfmisc_1(sK0)))) ),
    inference(forward_demodulation,[],[f22371,f22372])).

fof(f22372,plain,(
    k4_xboole_0(sK0,k1_setfam_1(k1_zfmisc_1(sK0))) = k3_subset_1(sK0,k1_setfam_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f3381,f1084])).

fof(f22371,plain,(
    k1_setfam_1(k1_zfmisc_1(sK0)) = k3_subset_1(sK0,k3_subset_1(sK0,k1_setfam_1(k1_zfmisc_1(sK0)))) ),
    inference(unit_resulting_resolution,[],[f3381,f1083])).

fof(f1083,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f715])).

fof(f715,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f35549,plain,(
    k3_subset_1(sK0,k7_subset_1(sK0,sK0,k3_tarski(k7_setfam_1(sK0,sK1)))) = k4_subset_1(sK0,k3_subset_1(sK0,sK0),k3_tarski(k7_setfam_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f34956,f923])).

fof(f34956,plain,(
    k3_subset_1(sK0,k7_subset_1(sK0,k2_subset_1(sK0),k3_tarski(k7_setfam_1(sK0,sK1)))) = k4_subset_1(sK0,k3_subset_1(sK0,k2_subset_1(sK0)),k3_tarski(k7_setfam_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f922,f4118,f913])).
%------------------------------------------------------------------------------
