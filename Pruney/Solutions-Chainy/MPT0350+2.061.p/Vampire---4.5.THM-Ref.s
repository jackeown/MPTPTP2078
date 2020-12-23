%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:59 EST 2020

% Result     : Theorem 6.46s
% Output     : Refutation 6.46s
% Verified   : 
% Statistics : Number of formulae       :  148 (1410 expanded)
%              Number of leaves         :   25 ( 420 expanded)
%              Depth                    :   31
%              Number of atoms          :  203 (2505 expanded)
%              Number of equality atoms :  123 ( 880 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6855,plain,(
    $false ),
    inference(global_subsumption,[],[f241,f6854])).

fof(f6854,plain,(
    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f6853,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f6853,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f6852,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f6852,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f6851,f148])).

fof(f148,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f59,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f6851,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f6850,f42])).

fof(f6850,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f6849,f118])).

fof(f118,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f113,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f113,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f103,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f103,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f98,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f98,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f34,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f6849,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f6848,f41])).

fof(f6848,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f6847,f3860])).

fof(f3860,plain,(
    ! [X2] : k3_xboole_0(sK1,X2) = k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X2,sK1))) ),
    inference(forward_demodulation,[],[f3859,f2481])).

fof(f2481,plain,(
    ! [X0] : k3_xboole_0(sK1,X0) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X0,sK0)),sK1) ),
    inference(forward_demodulation,[],[f2480,f416])).

fof(f416,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f154,f42])).

fof(f154,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f140,f78])).

fof(f78,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f42,f40])).

fof(f140,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f59,f39])).

fof(f2480,plain,(
    ! [X0] : k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X0,sK0))) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X0,sK0)),sK1) ),
    inference(forward_demodulation,[],[f2479,f2314])).

fof(f2314,plain,(
    ! [X8,X7] : k3_xboole_0(sK1,k5_xboole_0(X8,k5_xboole_0(X7,sK1))) = k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f2281,f42])).

fof(f2281,plain,(
    ! [X8,X7] : k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X7,X8),sK0)) = k3_xboole_0(sK1,k5_xboole_0(X8,k5_xboole_0(X7,sK1))) ),
    inference(superposition,[],[f1230,f142])).

fof(f142,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6) ),
    inference(superposition,[],[f59,f42])).

fof(f1230,plain,(
    ! [X19] : k3_xboole_0(sK1,k5_xboole_0(X19,sK1)) = k3_xboole_0(sK1,k5_xboole_0(X19,sK0)) ),
    inference(forward_demodulation,[],[f1229,f41])).

fof(f1229,plain,(
    ! [X19] : k3_xboole_0(k5_xboole_0(X19,sK0),sK1) = k3_xboole_0(sK1,k5_xboole_0(X19,sK1)) ),
    inference(forward_demodulation,[],[f1185,f1225])).

fof(f1225,plain,(
    ! [X14,X15] : k5_xboole_0(k3_xboole_0(X14,X15),X14) = k3_xboole_0(X14,k5_xboole_0(X15,X14)) ),
    inference(forward_demodulation,[],[f1182,f41])).

fof(f1182,plain,(
    ! [X14,X15] : k3_xboole_0(k5_xboole_0(X15,X14),X14) = k5_xboole_0(k3_xboole_0(X14,X15),X14) ),
    inference(superposition,[],[f169,f311])).

fof(f311,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f307,f51])).

fof(f307,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f301,f75])).

fof(f301,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f36,f239,f50])).

fof(f239,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f125,f238])).

fof(f238,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f237,f40])).

fof(f237,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f212,f203])).

fof(f203,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f112,f41])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f37,f51])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f212,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f93,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f36,f89,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f37,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f125,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f93,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f169,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k5_xboole_0(X3,X5),X4) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X5,X4)) ),
    inference(superposition,[],[f60,f41])).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f1185,plain,(
    ! [X19] : k3_xboole_0(k5_xboole_0(X19,sK0),sK1) = k5_xboole_0(k3_xboole_0(sK1,X19),sK1) ),
    inference(superposition,[],[f169,f118])).

fof(f2479,plain,(
    ! [X0] : k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X0,sK1))) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X0,sK0)),sK1) ),
    inference(forward_demodulation,[],[f2478,f2470])).

fof(f2470,plain,(
    ! [X10,X11] : k3_xboole_0(sK1,k5_xboole_0(X11,k5_xboole_0(sK0,X10))) = k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f2469,f42])).

fof(f2469,plain,(
    ! [X10,X11] : k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X10,X11),sK0)) = k3_xboole_0(sK1,k5_xboole_0(X11,k5_xboole_0(sK0,X10))) ),
    inference(forward_demodulation,[],[f2429,f41])).

fof(f2429,plain,(
    ! [X10,X11] : k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X10,X11),sK0)) = k3_xboole_0(k5_xboole_0(X11,k5_xboole_0(sK0,X10)),sK1) ),
    inference(superposition,[],[f1531,f148])).

fof(f1531,plain,(
    ! [X19] : k3_xboole_0(sK1,k5_xboole_0(X19,sK0)) = k3_xboole_0(k5_xboole_0(sK0,X19),sK1) ),
    inference(forward_demodulation,[],[f1530,f1230])).

fof(f1530,plain,(
    ! [X19] : k3_xboole_0(sK1,k5_xboole_0(X19,sK1)) = k3_xboole_0(k5_xboole_0(sK0,X19),sK1) ),
    inference(forward_demodulation,[],[f1487,f413])).

fof(f413,plain,(
    ! [X6,X5] : k5_xboole_0(k3_xboole_0(X6,X5),X5) = k3_xboole_0(X5,k5_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f408,f41])).

fof(f408,plain,(
    ! [X6,X5] : k3_xboole_0(k5_xboole_0(X6,X5),X5) = k5_xboole_0(k3_xboole_0(X6,X5),X5) ),
    inference(superposition,[],[f60,f311])).

fof(f1487,plain,(
    ! [X19] : k3_xboole_0(k5_xboole_0(sK0,X19),sK1) = k5_xboole_0(k3_xboole_0(X19,sK1),sK1) ),
    inference(superposition,[],[f179,f118])).

fof(f179,plain,(
    ! [X6,X7,X5] : k5_xboole_0(k3_xboole_0(X7,X6),k3_xboole_0(X5,X6)) = k3_xboole_0(k5_xboole_0(X5,X7),X6) ),
    inference(superposition,[],[f60,f42])).

fof(f2478,plain,(
    ! [X0] : k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,X0))) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X0,sK0)),sK1) ),
    inference(forward_demodulation,[],[f2438,f2276])).

fof(f2276,plain,(
    ! [X2] : k3_xboole_0(sK1,k5_xboole_0(X2,sK0)) = k3_xboole_0(sK1,k5_xboole_0(sK1,X2)) ),
    inference(superposition,[],[f1230,f42])).

fof(f2438,plain,(
    ! [X0] : k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,X0),sK0)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X0,sK0)),sK1) ),
    inference(superposition,[],[f188,f1531])).

fof(f188,plain,(
    ! [X10] : k5_xboole_0(k3_xboole_0(X10,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X10,sK0)) ),
    inference(forward_demodulation,[],[f177,f41])).

fof(f177,plain,(
    ! [X10] : k3_xboole_0(k5_xboole_0(X10,sK0),sK1) = k5_xboole_0(k3_xboole_0(X10,sK1),sK1) ),
    inference(superposition,[],[f60,f118])).

fof(f3859,plain,(
    ! [X2] : k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X2,sK1))) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X2,sK0)),sK1) ),
    inference(forward_demodulation,[],[f3858,f2314])).

fof(f3858,plain,(
    ! [X2] : k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X2,sK0)),sK1) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(X2,sK1))) ),
    inference(forward_demodulation,[],[f3808,f2276])).

fof(f3808,plain,(
    ! [X2] : k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X2,sK0)),sK1) = k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X2,sK1),sK0)) ),
    inference(superposition,[],[f537,f1230])).

fof(f537,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(sK1,X1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) ),
    inference(superposition,[],[f188,f41])).

fof(f6847,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f6665,f2314])).

fof(f6665,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f34,f242,f1292])).

fof(f1292,plain,(
    ! [X6,X4,X5] :
      ( k4_subset_1(X6,X4,X5) = k5_xboole_0(X5,k3_xboole_0(X4,k5_xboole_0(X4,X5)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6)) ) ),
    inference(backward_demodulation,[],[f403,f1288])).

fof(f1288,plain,(
    ! [X14,X15] : k3_xboole_0(X14,k5_xboole_0(X14,X15)) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(forward_demodulation,[],[f1247,f41])).

fof(f1247,plain,(
    ! [X14,X15] : k3_xboole_0(k5_xboole_0(X14,X15),X14) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(superposition,[],[f174,f311])).

fof(f174,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k5_xboole_0(X5,X3),X4) = k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f60,f41])).

fof(f403,plain,(
    ! [X6,X4,X5] :
      ( k4_subset_1(X6,X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k3_xboole_0(X4,X5)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6)) ) ),
    inference(forward_demodulation,[],[f402,f42])).

fof(f402,plain,(
    ! [X6,X4,X5] :
      ( k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X4,X5),X4)) = k4_subset_1(X6,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6)) ) ),
    inference(forward_demodulation,[],[f401,f148])).

fof(f401,plain,(
    ! [X6,X4,X5] :
      ( k5_xboole_0(k3_xboole_0(X4,X5),k5_xboole_0(X4,X5)) = k4_subset_1(X6,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6)) ) ),
    inference(forward_demodulation,[],[f395,f42])).

fof(f395,plain,(
    ! [X6,X4,X5] :
      ( k5_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k4_subset_1(X6,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f74,f72])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f61,f71])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f242,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f124,f240])).

fof(f240,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f211,f118])).

fof(f211,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f34,f73])).

fof(f124,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f52])).

fof(f241,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f77,f240])).

fof(f77,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f35,f38])).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f35,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (19671)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (19681)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (19679)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (19667)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (19689)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (19676)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (19673)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (19687)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (19664)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (19677)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (19681)Refutation not found, incomplete strategy% (19681)------------------------------
% 0.21/0.51  % (19681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19681)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19681)Memory used [KB]: 10618
% 0.21/0.51  % (19681)Time elapsed: 0.108 s
% 0.21/0.51  % (19681)------------------------------
% 0.21/0.51  % (19681)------------------------------
% 0.21/0.52  % (19678)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (19668)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (19666)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (19670)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (19669)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (19686)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (19691)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (19680)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (19665)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (19686)Refutation not found, incomplete strategy% (19686)------------------------------
% 0.21/0.53  % (19686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19685)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (19686)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19686)Memory used [KB]: 10746
% 0.21/0.53  % (19686)Time elapsed: 0.108 s
% 0.21/0.53  % (19686)------------------------------
% 0.21/0.53  % (19686)------------------------------
% 0.21/0.54  % (19674)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (19682)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (19688)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (19675)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (19683)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (19672)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (19692)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (19693)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (19690)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (19684)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.10/0.65  % (19694)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.67/0.70  % (19695)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.23/0.83  % (19669)Time limit reached!
% 3.23/0.83  % (19669)------------------------------
% 3.23/0.83  % (19669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.23/0.84  % (19669)Termination reason: Time limit
% 3.23/0.84  % (19669)Termination phase: Saturation
% 3.23/0.84  
% 3.23/0.84  % (19669)Memory used [KB]: 10362
% 3.23/0.84  % (19669)Time elapsed: 0.400 s
% 3.23/0.84  % (19669)------------------------------
% 3.23/0.84  % (19669)------------------------------
% 4.18/0.90  % (19674)Time limit reached!
% 4.18/0.90  % (19674)------------------------------
% 4.18/0.90  % (19674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.91  % (19676)Time limit reached!
% 4.18/0.91  % (19676)------------------------------
% 4.18/0.91  % (19676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.91  % (19676)Termination reason: Time limit
% 4.18/0.91  
% 4.18/0.91  % (19676)Memory used [KB]: 10746
% 4.18/0.91  % (19676)Time elapsed: 0.508 s
% 4.18/0.91  % (19676)------------------------------
% 4.18/0.91  % (19676)------------------------------
% 4.18/0.91  % (19674)Termination reason: Time limit
% 4.18/0.91  % (19674)Termination phase: Saturation
% 4.18/0.91  
% 4.18/0.91  % (19674)Memory used [KB]: 12537
% 4.18/0.91  % (19674)Time elapsed: 0.500 s
% 4.18/0.91  % (19674)------------------------------
% 4.18/0.91  % (19674)------------------------------
% 4.18/0.92  % (19665)Time limit reached!
% 4.18/0.92  % (19665)------------------------------
% 4.18/0.92  % (19665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/0.93  % (19665)Termination reason: Time limit
% 4.44/0.93  
% 4.44/0.93  % (19665)Memory used [KB]: 8699
% 4.44/0.93  % (19665)Time elapsed: 0.507 s
% 4.44/0.93  % (19665)------------------------------
% 4.44/0.93  % (19665)------------------------------
% 4.44/0.95  % (19696)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.44/0.96  % (19664)Time limit reached!
% 4.44/0.96  % (19664)------------------------------
% 4.44/0.96  % (19664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/0.96  % (19664)Termination reason: Time limit
% 4.44/0.96  
% 4.44/0.96  % (19664)Memory used [KB]: 4605
% 4.44/0.96  % (19664)Time elapsed: 0.515 s
% 4.44/0.96  % (19664)------------------------------
% 4.44/0.96  % (19664)------------------------------
% 4.93/1.02  % (19680)Time limit reached!
% 4.93/1.02  % (19680)------------------------------
% 4.93/1.02  % (19680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.02  % (19692)Time limit reached!
% 4.93/1.02  % (19692)------------------------------
% 4.93/1.02  % (19692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.02  % (19692)Termination reason: Time limit
% 4.93/1.02  % (19692)Termination phase: Saturation
% 4.93/1.02  
% 4.93/1.02  % (19692)Memory used [KB]: 11001
% 4.93/1.02  % (19692)Time elapsed: 0.600 s
% 4.93/1.02  % (19692)------------------------------
% 4.93/1.02  % (19692)------------------------------
% 4.93/1.02  % (19680)Termination reason: Time limit
% 4.93/1.02  % (19680)Termination phase: Saturation
% 4.93/1.02  
% 4.93/1.02  % (19680)Memory used [KB]: 17270
% 4.93/1.02  % (19680)Time elapsed: 0.600 s
% 4.93/1.02  % (19680)------------------------------
% 4.93/1.02  % (19680)------------------------------
% 4.93/1.02  % (19698)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.93/1.05  % (19697)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.93/1.05  % (19671)Time limit reached!
% 4.93/1.05  % (19671)------------------------------
% 4.93/1.05  % (19671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.05  % (19671)Termination reason: Time limit
% 4.93/1.05  % (19671)Termination phase: Saturation
% 4.93/1.05  
% 4.93/1.05  % (19671)Memory used [KB]: 11129
% 4.93/1.05  % (19671)Time elapsed: 0.600 s
% 4.93/1.05  % (19671)------------------------------
% 4.93/1.05  % (19671)------------------------------
% 4.93/1.07  % (19699)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.43/1.10  % (19700)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.43/1.16  % (19701)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.43/1.17  % (19702)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.46/1.19  % (19688)Refutation found. Thanks to Tanya!
% 6.46/1.19  % SZS status Theorem for theBenchmark
% 6.46/1.19  % SZS output start Proof for theBenchmark
% 6.46/1.19  fof(f6855,plain,(
% 6.46/1.19    $false),
% 6.46/1.19    inference(global_subsumption,[],[f241,f6854])).
% 6.46/1.19  fof(f6854,plain,(
% 6.46/1.19    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 6.46/1.19    inference(forward_demodulation,[],[f6853,f40])).
% 6.46/1.19  fof(f40,plain,(
% 6.46/1.19    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.46/1.19    inference(cnf_transformation,[],[f7])).
% 6.46/1.19  fof(f7,axiom,(
% 6.46/1.19    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 6.46/1.19  fof(f6853,plain,(
% 6.46/1.19    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 6.46/1.19    inference(forward_demodulation,[],[f6852,f39])).
% 6.46/1.19  fof(f39,plain,(
% 6.46/1.19    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f9])).
% 6.46/1.19  fof(f9,axiom,(
% 6.46/1.19    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 6.46/1.19  fof(f6852,plain,(
% 6.46/1.19    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 6.46/1.19    inference(forward_demodulation,[],[f6851,f148])).
% 6.46/1.19  fof(f148,plain,(
% 6.46/1.19    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 6.46/1.19    inference(superposition,[],[f59,f42])).
% 6.46/1.19  fof(f42,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f2])).
% 6.46/1.19  fof(f2,axiom,(
% 6.46/1.19    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 6.46/1.19  fof(f59,plain,(
% 6.46/1.19    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 6.46/1.19    inference(cnf_transformation,[],[f8])).
% 6.46/1.19  fof(f8,axiom,(
% 6.46/1.19    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 6.46/1.19  fof(f6851,plain,(
% 6.46/1.19    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 6.46/1.19    inference(forward_demodulation,[],[f6850,f42])).
% 6.46/1.19  fof(f6850,plain,(
% 6.46/1.19    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 6.46/1.19    inference(forward_demodulation,[],[f6849,f118])).
% 6.46/1.19  fof(f118,plain,(
% 6.46/1.19    sK1 = k3_xboole_0(sK0,sK1)),
% 6.46/1.19    inference(superposition,[],[f113,f41])).
% 6.46/1.19  fof(f41,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f1])).
% 6.46/1.19  fof(f1,axiom,(
% 6.46/1.19    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.46/1.19  fof(f113,plain,(
% 6.46/1.19    sK1 = k3_xboole_0(sK1,sK0)),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f103,f51])).
% 6.46/1.19  fof(f51,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f29])).
% 6.46/1.19  fof(f29,plain,(
% 6.46/1.19    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.46/1.19    inference(ennf_transformation,[],[f5])).
% 6.46/1.19  fof(f5,axiom,(
% 6.46/1.19    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.46/1.19  fof(f103,plain,(
% 6.46/1.19    r1_tarski(sK1,sK0)),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f98,f75])).
% 6.46/1.19  fof(f75,plain,(
% 6.46/1.19    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 6.46/1.19    inference(equality_resolution,[],[f55])).
% 6.46/1.19  fof(f55,plain,(
% 6.46/1.19    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 6.46/1.19    inference(cnf_transformation,[],[f17])).
% 6.46/1.19  fof(f17,axiom,(
% 6.46/1.19    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 6.46/1.19  fof(f98,plain,(
% 6.46/1.19    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f36,f34,f50])).
% 6.46/1.19  fof(f50,plain,(
% 6.46/1.19    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f28])).
% 6.46/1.19  fof(f28,plain,(
% 6.46/1.19    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 6.46/1.19    inference(ennf_transformation,[],[f19])).
% 6.46/1.19  fof(f19,axiom,(
% 6.46/1.19    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 6.46/1.19  fof(f34,plain,(
% 6.46/1.19    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 6.46/1.19    inference(cnf_transformation,[],[f27])).
% 6.46/1.19  fof(f27,plain,(
% 6.46/1.19    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.46/1.19    inference(ennf_transformation,[],[f26])).
% 6.46/1.19  fof(f26,negated_conjecture,(
% 6.46/1.19    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 6.46/1.19    inference(negated_conjecture,[],[f25])).
% 6.46/1.19  fof(f25,conjecture,(
% 6.46/1.19    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 6.46/1.19  fof(f36,plain,(
% 6.46/1.19    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 6.46/1.19    inference(cnf_transformation,[],[f23])).
% 6.46/1.19  fof(f23,axiom,(
% 6.46/1.19    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 6.46/1.19  fof(f6849,plain,(
% 6.46/1.19    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 6.46/1.19    inference(forward_demodulation,[],[f6848,f41])).
% 6.46/1.19  fof(f6848,plain,(
% 6.46/1.19    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK0))),
% 6.46/1.19    inference(forward_demodulation,[],[f6847,f3860])).
% 6.46/1.19  fof(f3860,plain,(
% 6.46/1.19    ( ! [X2] : (k3_xboole_0(sK1,X2) = k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X2,sK1)))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f3859,f2481])).
% 6.46/1.19  fof(f2481,plain,(
% 6.46/1.19    ( ! [X0] : (k3_xboole_0(sK1,X0) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X0,sK0)),sK1)) )),
% 6.46/1.19    inference(forward_demodulation,[],[f2480,f416])).
% 6.46/1.19  fof(f416,plain,(
% 6.46/1.19    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 6.46/1.19    inference(superposition,[],[f154,f42])).
% 6.46/1.19  fof(f154,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 6.46/1.19    inference(forward_demodulation,[],[f140,f78])).
% 6.46/1.19  fof(f78,plain,(
% 6.46/1.19    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 6.46/1.19    inference(superposition,[],[f42,f40])).
% 6.46/1.19  fof(f140,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 6.46/1.19    inference(superposition,[],[f59,f39])).
% 6.46/1.19  fof(f2480,plain,(
% 6.46/1.19    ( ! [X0] : (k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X0,sK0))) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X0,sK0)),sK1)) )),
% 6.46/1.19    inference(forward_demodulation,[],[f2479,f2314])).
% 6.46/1.19  fof(f2314,plain,(
% 6.46/1.19    ( ! [X8,X7] : (k3_xboole_0(sK1,k5_xboole_0(X8,k5_xboole_0(X7,sK1))) = k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X7,X8)))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f2281,f42])).
% 6.46/1.19  fof(f2281,plain,(
% 6.46/1.19    ( ! [X8,X7] : (k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X7,X8),sK0)) = k3_xboole_0(sK1,k5_xboole_0(X8,k5_xboole_0(X7,sK1)))) )),
% 6.46/1.19    inference(superposition,[],[f1230,f142])).
% 6.46/1.19  fof(f142,plain,(
% 6.46/1.19    ( ! [X6,X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6)) )),
% 6.46/1.19    inference(superposition,[],[f59,f42])).
% 6.46/1.19  fof(f1230,plain,(
% 6.46/1.19    ( ! [X19] : (k3_xboole_0(sK1,k5_xboole_0(X19,sK1)) = k3_xboole_0(sK1,k5_xboole_0(X19,sK0))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f1229,f41])).
% 6.46/1.19  fof(f1229,plain,(
% 6.46/1.19    ( ! [X19] : (k3_xboole_0(k5_xboole_0(X19,sK0),sK1) = k3_xboole_0(sK1,k5_xboole_0(X19,sK1))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f1185,f1225])).
% 6.46/1.19  fof(f1225,plain,(
% 6.46/1.19    ( ! [X14,X15] : (k5_xboole_0(k3_xboole_0(X14,X15),X14) = k3_xboole_0(X14,k5_xboole_0(X15,X14))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f1182,f41])).
% 6.46/1.19  fof(f1182,plain,(
% 6.46/1.19    ( ! [X14,X15] : (k3_xboole_0(k5_xboole_0(X15,X14),X14) = k5_xboole_0(k3_xboole_0(X14,X15),X14)) )),
% 6.46/1.19    inference(superposition,[],[f169,f311])).
% 6.46/1.19  fof(f311,plain,(
% 6.46/1.19    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f307,f51])).
% 6.46/1.19  fof(f307,plain,(
% 6.46/1.19    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f301,f75])).
% 6.46/1.19  fof(f301,plain,(
% 6.46/1.19    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f36,f239,f50])).
% 6.46/1.19  fof(f239,plain,(
% 6.46/1.19    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 6.46/1.19    inference(backward_demodulation,[],[f125,f238])).
% 6.46/1.19  fof(f238,plain,(
% 6.46/1.19    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 6.46/1.19    inference(forward_demodulation,[],[f237,f40])).
% 6.46/1.19  fof(f237,plain,(
% 6.46/1.19    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 6.46/1.19    inference(forward_demodulation,[],[f212,f203])).
% 6.46/1.19  fof(f203,plain,(
% 6.46/1.19    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 6.46/1.19    inference(superposition,[],[f112,f41])).
% 6.46/1.19  fof(f112,plain,(
% 6.46/1.19    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f37,f51])).
% 6.46/1.19  fof(f37,plain,(
% 6.46/1.19    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f6])).
% 6.46/1.19  fof(f6,axiom,(
% 6.46/1.19    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 6.46/1.19  fof(f212,plain,(
% 6.46/1.19    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f93,f73])).
% 6.46/1.19  fof(f73,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.46/1.19    inference(definition_unfolding,[],[f53,f45])).
% 6.46/1.19  fof(f45,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.46/1.19    inference(cnf_transformation,[],[f3])).
% 6.46/1.19  fof(f3,axiom,(
% 6.46/1.19    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.46/1.19  fof(f53,plain,(
% 6.46/1.19    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f31])).
% 6.46/1.19  fof(f31,plain,(
% 6.46/1.19    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.46/1.19    inference(ennf_transformation,[],[f21])).
% 6.46/1.19  fof(f21,axiom,(
% 6.46/1.19    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 6.46/1.19  fof(f93,plain,(
% 6.46/1.19    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f36,f89,f49])).
% 6.46/1.19  fof(f49,plain,(
% 6.46/1.19    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f28])).
% 6.46/1.19  fof(f89,plain,(
% 6.46/1.19    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f37,f76])).
% 6.46/1.19  fof(f76,plain,(
% 6.46/1.19    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 6.46/1.19    inference(equality_resolution,[],[f54])).
% 6.46/1.19  fof(f54,plain,(
% 6.46/1.19    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 6.46/1.19    inference(cnf_transformation,[],[f17])).
% 6.46/1.19  fof(f125,plain,(
% 6.46/1.19    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f93,f52])).
% 6.46/1.19  fof(f52,plain,(
% 6.46/1.19    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.46/1.19    inference(cnf_transformation,[],[f30])).
% 6.46/1.19  fof(f30,plain,(
% 6.46/1.19    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.46/1.19    inference(ennf_transformation,[],[f22])).
% 6.46/1.19  fof(f22,axiom,(
% 6.46/1.19    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 6.46/1.19  fof(f169,plain,(
% 6.46/1.19    ( ! [X4,X5,X3] : (k3_xboole_0(k5_xboole_0(X3,X5),X4) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X5,X4))) )),
% 6.46/1.19    inference(superposition,[],[f60,f41])).
% 6.46/1.19  fof(f60,plain,(
% 6.46/1.19    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f4])).
% 6.46/1.19  fof(f4,axiom,(
% 6.46/1.19    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 6.46/1.19  fof(f1185,plain,(
% 6.46/1.19    ( ! [X19] : (k3_xboole_0(k5_xboole_0(X19,sK0),sK1) = k5_xboole_0(k3_xboole_0(sK1,X19),sK1)) )),
% 6.46/1.19    inference(superposition,[],[f169,f118])).
% 6.46/1.19  fof(f2479,plain,(
% 6.46/1.19    ( ! [X0] : (k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X0,sK1))) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X0,sK0)),sK1)) )),
% 6.46/1.19    inference(forward_demodulation,[],[f2478,f2470])).
% 6.46/1.19  fof(f2470,plain,(
% 6.46/1.19    ( ! [X10,X11] : (k3_xboole_0(sK1,k5_xboole_0(X11,k5_xboole_0(sK0,X10))) = k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X10,X11)))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f2469,f42])).
% 6.46/1.19  fof(f2469,plain,(
% 6.46/1.19    ( ! [X10,X11] : (k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X10,X11),sK0)) = k3_xboole_0(sK1,k5_xboole_0(X11,k5_xboole_0(sK0,X10)))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f2429,f41])).
% 6.46/1.19  fof(f2429,plain,(
% 6.46/1.19    ( ! [X10,X11] : (k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X10,X11),sK0)) = k3_xboole_0(k5_xboole_0(X11,k5_xboole_0(sK0,X10)),sK1)) )),
% 6.46/1.19    inference(superposition,[],[f1531,f148])).
% 6.46/1.19  fof(f1531,plain,(
% 6.46/1.19    ( ! [X19] : (k3_xboole_0(sK1,k5_xboole_0(X19,sK0)) = k3_xboole_0(k5_xboole_0(sK0,X19),sK1)) )),
% 6.46/1.19    inference(forward_demodulation,[],[f1530,f1230])).
% 6.46/1.19  fof(f1530,plain,(
% 6.46/1.19    ( ! [X19] : (k3_xboole_0(sK1,k5_xboole_0(X19,sK1)) = k3_xboole_0(k5_xboole_0(sK0,X19),sK1)) )),
% 6.46/1.19    inference(forward_demodulation,[],[f1487,f413])).
% 6.46/1.19  fof(f413,plain,(
% 6.46/1.19    ( ! [X6,X5] : (k5_xboole_0(k3_xboole_0(X6,X5),X5) = k3_xboole_0(X5,k5_xboole_0(X6,X5))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f408,f41])).
% 6.46/1.19  fof(f408,plain,(
% 6.46/1.19    ( ! [X6,X5] : (k3_xboole_0(k5_xboole_0(X6,X5),X5) = k5_xboole_0(k3_xboole_0(X6,X5),X5)) )),
% 6.46/1.19    inference(superposition,[],[f60,f311])).
% 6.46/1.19  fof(f1487,plain,(
% 6.46/1.19    ( ! [X19] : (k3_xboole_0(k5_xboole_0(sK0,X19),sK1) = k5_xboole_0(k3_xboole_0(X19,sK1),sK1)) )),
% 6.46/1.19    inference(superposition,[],[f179,f118])).
% 6.46/1.19  fof(f179,plain,(
% 6.46/1.19    ( ! [X6,X7,X5] : (k5_xboole_0(k3_xboole_0(X7,X6),k3_xboole_0(X5,X6)) = k3_xboole_0(k5_xboole_0(X5,X7),X6)) )),
% 6.46/1.19    inference(superposition,[],[f60,f42])).
% 6.46/1.19  fof(f2478,plain,(
% 6.46/1.19    ( ! [X0] : (k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,X0))) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X0,sK0)),sK1)) )),
% 6.46/1.19    inference(forward_demodulation,[],[f2438,f2276])).
% 6.46/1.19  fof(f2276,plain,(
% 6.46/1.19    ( ! [X2] : (k3_xboole_0(sK1,k5_xboole_0(X2,sK0)) = k3_xboole_0(sK1,k5_xboole_0(sK1,X2))) )),
% 6.46/1.19    inference(superposition,[],[f1230,f42])).
% 6.46/1.19  fof(f2438,plain,(
% 6.46/1.19    ( ! [X0] : (k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,X0),sK0)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X0,sK0)),sK1)) )),
% 6.46/1.19    inference(superposition,[],[f188,f1531])).
% 6.46/1.19  fof(f188,plain,(
% 6.46/1.19    ( ! [X10] : (k5_xboole_0(k3_xboole_0(X10,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X10,sK0))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f177,f41])).
% 6.46/1.19  fof(f177,plain,(
% 6.46/1.19    ( ! [X10] : (k3_xboole_0(k5_xboole_0(X10,sK0),sK1) = k5_xboole_0(k3_xboole_0(X10,sK1),sK1)) )),
% 6.46/1.19    inference(superposition,[],[f60,f118])).
% 6.46/1.19  fof(f3859,plain,(
% 6.46/1.19    ( ! [X2] : (k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X2,sK1))) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X2,sK0)),sK1)) )),
% 6.46/1.19    inference(forward_demodulation,[],[f3858,f2314])).
% 6.46/1.19  fof(f3858,plain,(
% 6.46/1.19    ( ! [X2] : (k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X2,sK0)),sK1) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(X2,sK1)))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f3808,f2276])).
% 6.46/1.19  fof(f3808,plain,(
% 6.46/1.19    ( ! [X2] : (k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(X2,sK0)),sK1) = k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X2,sK1),sK0))) )),
% 6.46/1.19    inference(superposition,[],[f537,f1230])).
% 6.46/1.19  fof(f537,plain,(
% 6.46/1.19    ( ! [X1] : (k5_xboole_0(k3_xboole_0(sK1,X1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0))) )),
% 6.46/1.19    inference(superposition,[],[f188,f41])).
% 6.46/1.19  fof(f6847,plain,(
% 6.46/1.19    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))))),
% 6.46/1.19    inference(forward_demodulation,[],[f6665,f2314])).
% 6.46/1.19  fof(f6665,plain,(
% 6.46/1.19    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f34,f242,f1292])).
% 6.46/1.19  fof(f1292,plain,(
% 6.46/1.19    ( ! [X6,X4,X5] : (k4_subset_1(X6,X4,X5) = k5_xboole_0(X5,k3_xboole_0(X4,k5_xboole_0(X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~m1_subset_1(X4,k1_zfmisc_1(X6))) )),
% 6.46/1.19    inference(backward_demodulation,[],[f403,f1288])).
% 6.46/1.19  fof(f1288,plain,(
% 6.46/1.19    ( ! [X14,X15] : (k3_xboole_0(X14,k5_xboole_0(X14,X15)) = k5_xboole_0(X14,k3_xboole_0(X14,X15))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f1247,f41])).
% 6.46/1.19  fof(f1247,plain,(
% 6.46/1.19    ( ! [X14,X15] : (k3_xboole_0(k5_xboole_0(X14,X15),X14) = k5_xboole_0(X14,k3_xboole_0(X14,X15))) )),
% 6.46/1.19    inference(superposition,[],[f174,f311])).
% 6.46/1.19  fof(f174,plain,(
% 6.46/1.19    ( ! [X4,X5,X3] : (k3_xboole_0(k5_xboole_0(X5,X3),X4) = k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(X4,X3))) )),
% 6.46/1.19    inference(superposition,[],[f60,f41])).
% 6.46/1.19  fof(f403,plain,(
% 6.46/1.19    ( ! [X6,X4,X5] : (k4_subset_1(X6,X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k3_xboole_0(X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~m1_subset_1(X4,k1_zfmisc_1(X6))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f402,f42])).
% 6.46/1.19  fof(f402,plain,(
% 6.46/1.19    ( ! [X6,X4,X5] : (k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X4,X5),X4)) = k4_subset_1(X6,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~m1_subset_1(X4,k1_zfmisc_1(X6))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f401,f148])).
% 6.46/1.19  fof(f401,plain,(
% 6.46/1.19    ( ! [X6,X4,X5] : (k5_xboole_0(k3_xboole_0(X4,X5),k5_xboole_0(X4,X5)) = k4_subset_1(X6,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~m1_subset_1(X4,k1_zfmisc_1(X6))) )),
% 6.46/1.19    inference(forward_demodulation,[],[f395,f42])).
% 6.46/1.19  fof(f395,plain,(
% 6.46/1.19    ( ! [X6,X4,X5] : (k5_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k4_subset_1(X6,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~m1_subset_1(X4,k1_zfmisc_1(X6))) )),
% 6.46/1.19    inference(superposition,[],[f74,f72])).
% 6.46/1.19  fof(f72,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.46/1.19    inference(definition_unfolding,[],[f46,f71])).
% 6.46/1.19  fof(f71,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.46/1.19    inference(definition_unfolding,[],[f43,f70])).
% 6.46/1.19  fof(f70,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.46/1.19    inference(definition_unfolding,[],[f44,f69])).
% 6.46/1.19  fof(f69,plain,(
% 6.46/1.19    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.46/1.19    inference(definition_unfolding,[],[f58,f68])).
% 6.46/1.19  fof(f68,plain,(
% 6.46/1.19    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.46/1.19    inference(definition_unfolding,[],[f62,f67])).
% 6.46/1.19  fof(f67,plain,(
% 6.46/1.19    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.46/1.19    inference(definition_unfolding,[],[f63,f66])).
% 6.46/1.19  fof(f66,plain,(
% 6.46/1.19    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.46/1.19    inference(definition_unfolding,[],[f64,f65])).
% 6.46/1.19  fof(f65,plain,(
% 6.46/1.19    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f16])).
% 6.46/1.19  fof(f16,axiom,(
% 6.46/1.19    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 6.46/1.19  fof(f64,plain,(
% 6.46/1.19    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f15])).
% 6.46/1.19  fof(f15,axiom,(
% 6.46/1.19    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 6.46/1.19  fof(f63,plain,(
% 6.46/1.19    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f14])).
% 6.46/1.19  fof(f14,axiom,(
% 6.46/1.19    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 6.46/1.19  fof(f62,plain,(
% 6.46/1.19    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f13])).
% 6.46/1.19  fof(f13,axiom,(
% 6.46/1.19    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 6.46/1.19  fof(f58,plain,(
% 6.46/1.19    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f12])).
% 6.46/1.19  fof(f12,axiom,(
% 6.46/1.19    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 6.46/1.19  fof(f44,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f11])).
% 6.46/1.19  fof(f11,axiom,(
% 6.46/1.19    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 6.46/1.19  fof(f43,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.46/1.19    inference(cnf_transformation,[],[f18])).
% 6.46/1.19  fof(f18,axiom,(
% 6.46/1.19    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 6.46/1.19  fof(f46,plain,(
% 6.46/1.19    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 6.46/1.19    inference(cnf_transformation,[],[f10])).
% 6.46/1.19  fof(f10,axiom,(
% 6.46/1.19    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 6.46/1.19  fof(f74,plain,(
% 6.46/1.19    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.46/1.19    inference(definition_unfolding,[],[f61,f71])).
% 6.46/1.19  fof(f61,plain,(
% 6.46/1.19    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 6.46/1.19    inference(cnf_transformation,[],[f33])).
% 6.46/1.19  fof(f33,plain,(
% 6.46/1.19    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.46/1.19    inference(flattening,[],[f32])).
% 6.46/1.19  fof(f32,plain,(
% 6.46/1.19    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 6.46/1.19    inference(ennf_transformation,[],[f24])).
% 6.46/1.19  fof(f24,axiom,(
% 6.46/1.19    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 6.46/1.19  fof(f242,plain,(
% 6.46/1.19    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 6.46/1.19    inference(backward_demodulation,[],[f124,f240])).
% 6.46/1.19  fof(f240,plain,(
% 6.46/1.19    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 6.46/1.19    inference(forward_demodulation,[],[f211,f118])).
% 6.46/1.19  fof(f211,plain,(
% 6.46/1.19    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f34,f73])).
% 6.46/1.19  fof(f124,plain,(
% 6.46/1.19    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 6.46/1.19    inference(unit_resulting_resolution,[],[f34,f52])).
% 6.46/1.19  fof(f241,plain,(
% 6.46/1.19    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 6.46/1.19    inference(backward_demodulation,[],[f77,f240])).
% 6.46/1.19  fof(f77,plain,(
% 6.46/1.19    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 6.46/1.19    inference(backward_demodulation,[],[f35,f38])).
% 6.46/1.19  fof(f38,plain,(
% 6.46/1.19    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 6.46/1.19    inference(cnf_transformation,[],[f20])).
% 6.46/1.19  fof(f20,axiom,(
% 6.46/1.19    ! [X0] : k2_subset_1(X0) = X0),
% 6.46/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 6.46/1.19  fof(f35,plain,(
% 6.46/1.19    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 6.46/1.19    inference(cnf_transformation,[],[f27])).
% 6.46/1.19  % SZS output end Proof for theBenchmark
% 6.46/1.19  % (19688)------------------------------
% 6.46/1.19  % (19688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.46/1.19  % (19688)Termination reason: Refutation
% 6.46/1.19  
% 6.46/1.19  % (19688)Memory used [KB]: 14456
% 6.46/1.19  % (19688)Time elapsed: 0.770 s
% 6.46/1.19  % (19688)------------------------------
% 6.46/1.19  % (19688)------------------------------
% 6.46/1.19  % (19663)Success in time 0.833 s
%------------------------------------------------------------------------------
