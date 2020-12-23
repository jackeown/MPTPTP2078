%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:33 EST 2020

% Result     : Theorem 16.52s
% Output     : Refutation 16.52s
% Verified   : 
% Statistics : Number of formulae       :  163 (1480 expanded)
%              Number of leaves         :   12 ( 352 expanded)
%              Depth                    :   50
%              Number of atoms          :  300 (3375 expanded)
%              Number of equality atoms :  124 (1420 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (363)Time limit reached!
% (363)------------------------------
% (363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (363)Termination reason: Time limit

% (363)Memory used [KB]: 13048
% (363)Time elapsed: 2.050 s
% (363)------------------------------
% (363)------------------------------
fof(f19841,plain,(
    $false ),
    inference(global_subsumption,[],[f2729,f16749,f19838])).

fof(f19838,plain,(
    r1_tarski(sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f19830])).

fof(f19830,plain,
    ( r1_tarski(sK2,sK0)
    | r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f19514,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f19514,plain,(
    ! [X18] :
      ( r2_hidden(sK5(sK2,X18),sK0)
      | r1_tarski(sK2,X18) ) ),
    inference(resolution,[],[f19482,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f19482,plain,(
    ! [X16] :
      ( ~ r2_hidden(X16,sK2)
      | r2_hidden(X16,sK0) ) ),
    inference(subsumption_resolution,[],[f19437,f9653])).

fof(f9653,plain,(
    ! [X8] : ~ r2_hidden(X8,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f9646,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f73,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f9646,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,k1_xboole_0)
      | ~ r2_hidden(X8,k4_xboole_0(X9,k2_zfmisc_1(k1_xboole_0,sK3))) ) ),
    inference(superposition,[],[f2036,f67])).

fof(f67,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2036,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(X13,k2_zfmisc_1(X14,sK1))
      | ~ r2_hidden(X13,k4_xboole_0(X15,k2_zfmisc_1(X14,sK3))) ) ),
    inference(resolution,[],[f1893,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1893,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,sK3))
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,sK1)) ) ),
    inference(resolution,[],[f1855,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1855,plain,(
    ! [X121] : r1_tarski(k2_zfmisc_1(X121,sK1),k2_zfmisc_1(X121,sK3)) ),
    inference(superposition,[],[f1160,f1328])).

fof(f1328,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f1324,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1324,plain,(
    r1_tarski(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f1315])).

fof(f1315,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3) ),
    inference(resolution,[],[f1284,f44])).

fof(f1284,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0,sK3),sK1)
      | r1_tarski(X0,sK3) ) ),
    inference(resolution,[],[f1279,f45])).

fof(f1279,plain,(
    ! [X17] :
      ( r2_hidden(X17,sK3)
      | ~ r2_hidden(X17,sK1) ) ),
    inference(subsumption_resolution,[],[f1245,f92])).

fof(f1245,plain,(
    ! [X17] :
      ( r2_hidden(X17,k1_xboole_0)
      | r2_hidden(X17,sK3)
      | ~ r2_hidden(X17,sK1) ) ),
    inference(superposition,[],[f68,f1229])).

fof(f1229,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f1224,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f1224,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f1217])).

fof(f1217,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f46,f1188])).

fof(f1188,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f1130,f210])).

fof(f210,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k3_xboole_0(k4_xboole_0(X7,X8),X7) ),
    inference(resolution,[],[f204,f38])).

fof(f204,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f81,f45])).

fof(f81,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK5(k4_xboole_0(X2,X3),X4),X2)
      | r1_tarski(k4_xboole_0(X2,X3),X4) ) ),
    inference(resolution,[],[f70,f44])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1130,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X3,sK3),sK1)) ),
    inference(superposition,[],[f224,f502])).

fof(f502,plain,(
    ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X13,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f436,f30])).

fof(f30,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f436,plain,(
    ! [X6,X8,X7,X9] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X8,k4_xboole_0(X6,X7)),k2_zfmisc_1(X9,X7)) ),
    inference(forward_demodulation,[],[f418,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f418,plain,(
    ! [X6,X8,X7,X9] : k3_xboole_0(k2_zfmisc_1(X8,k4_xboole_0(X6,X7)),k2_zfmisc_1(X9,X7)) = k2_zfmisc_1(k3_xboole_0(X8,X9),k1_xboole_0) ),
    inference(superposition,[],[f63,f392])).

fof(f392,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f391,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f391,plain,(
    ! [X4,X3] : v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) ),
    inference(duplicate_literal_removal,[],[f382])).

fof(f382,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))
      | v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) ) ),
    inference(resolution,[],[f153,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1)),X0)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f73,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X1))
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f84,f69])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1)),X1)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f72,f36])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f224,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(X3,k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f63,f37])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1160,plain,(
    ! [X76,X74,X75] : r1_tarski(k2_zfmisc_1(X74,k3_xboole_0(X75,X76)),k2_zfmisc_1(X74,X76)) ),
    inference(superposition,[],[f254,f224])).

fof(f254,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f85,f45])).

fof(f85,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK5(k3_xboole_0(X2,X3),X4),X3)
      | r1_tarski(k3_xboole_0(X2,X3),X4) ) ),
    inference(resolution,[],[f72,f44])).

fof(f19437,plain,(
    ! [X16] :
      ( r2_hidden(X16,k1_xboole_0)
      | r2_hidden(X16,sK0)
      | ~ r2_hidden(X16,sK2) ) ),
    inference(superposition,[],[f68,f19414])).

fof(f19414,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f19411,f35])).

fof(f19411,plain,(
    v1_xboole_0(k4_xboole_0(sK2,sK0)) ),
    inference(duplicate_literal_removal,[],[f19408])).

fof(f19408,plain,
    ( v1_xboole_0(k4_xboole_0(sK2,sK0))
    | v1_xboole_0(k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f19269,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k4_xboole_0(X0,X1)),X0)
      | v1_xboole_0(k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f70,f36])).

fof(f19269,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X2,sK0)),sK2)
      | v1_xboole_0(k4_xboole_0(X2,sK0)) ) ),
    inference(resolution,[],[f19251,f36])).

fof(f19251,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k4_xboole_0(X7,sK0))
      | ~ r2_hidden(X8,sK2) ) ),
    inference(subsumption_resolution,[],[f19205,f9653])).

fof(f19205,plain,(
    ! [X8,X7] :
      ( r2_hidden(X8,k1_xboole_0)
      | ~ r2_hidden(X8,k4_xboole_0(X7,sK0))
      | ~ r2_hidden(X8,sK2) ) ),
    inference(superposition,[],[f71,f19198])).

fof(f19198,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X4,sK0)) ),
    inference(subsumption_resolution,[],[f19196,f67])).

fof(f19196,plain,(
    ! [X4] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
      | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X4,sK0)) ) ),
    inference(superposition,[],[f4116,f750])).

fof(f750,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f749,f35])).

fof(f749,plain,(
    ! [X4,X3] : v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3))) ),
    inference(duplicate_literal_removal,[],[f731])).

fof(f731,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)))
      | v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3))) ) ),
    inference(resolution,[],[f165,f84])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X0))
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f89,f69])).

fof(f4116,plain,(
    ! [X11] :
      ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X11),sK1)
      | k1_xboole_0 = k3_xboole_0(sK2,X11) ) ),
    inference(subsumption_resolution,[],[f4098,f32])).

fof(f32,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f4098,plain,(
    ! [X11] :
      ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X11),sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = k3_xboole_0(sK2,X11) ) ),
    inference(superposition,[],[f46,f3466])).

fof(f3466,plain,(
    ! [X7] : k2_zfmisc_1(k3_xboole_0(sK2,X7),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,X7),sK1) ),
    inference(forward_demodulation,[],[f3393,f228])).

fof(f228,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X4,X3),k2_zfmisc_1(X5,X3)) = k2_zfmisc_1(k3_xboole_0(X4,X5),X3) ),
    inference(superposition,[],[f63,f37])).

fof(f3393,plain,(
    ! [X7] : k2_zfmisc_1(k3_xboole_0(sK2,X7),sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X7,sK1)) ),
    inference(superposition,[],[f228,f3310])).

fof(f3310,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(global_subsumption,[],[f1902,f3302])).

fof(f3302,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f3292,f30])).

fof(f3292,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1)) ),
    inference(superposition,[],[f3286,f37])).

fof(f3286,plain,(
    ! [X17] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X17,sK3)),k2_zfmisc_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f3285,f1128])).

fof(f1128,plain,(
    ! [X9] : k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f224,f30])).

fof(f3285,plain,(
    ! [X17] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK2,X17),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f3271,f63])).

fof(f3271,plain,(
    ! [X17] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,sK0),k3_xboole_0(X17,sK1)),k2_zfmisc_1(sK2,sK1)) ),
    inference(superposition,[],[f1160,f2474])).

fof(f2474,plain,(
    k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1) ),
    inference(superposition,[],[f228,f1903])).

fof(f1903,plain,(
    k2_zfmisc_1(sK2,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f1898,f38])).

fof(f1898,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f1855,f30])).

fof(f1902,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(resolution,[],[f1898,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f16749,plain,(
    sK0 != sK2 ),
    inference(trivial_inequality_removal,[],[f16748])).

fof(f16748,plain,
    ( sK1 != sK1
    | sK0 != sK2 ),
    inference(superposition,[],[f29,f12734])).

fof(f12734,plain,(
    sK1 = sK3 ),
    inference(resolution,[],[f12732,f1327])).

fof(f1327,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3 ),
    inference(resolution,[],[f1324,f41])).

fof(f12732,plain,(
    r1_tarski(sK3,sK1) ),
    inference(duplicate_literal_removal,[],[f12724])).

fof(f12724,plain,
    ( r1_tarski(sK3,sK1)
    | r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f12341,f45])).

fof(f12341,plain,(
    ! [X18] :
      ( r2_hidden(sK5(sK3,X18),sK1)
      | r1_tarski(sK3,X18) ) ),
    inference(resolution,[],[f12312,f44])).

fof(f12312,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,sK3)
      | r2_hidden(X9,sK1) ) ),
    inference(subsumption_resolution,[],[f12266,f9653])).

fof(f12266,plain,(
    ! [X9] :
      ( r2_hidden(X9,k1_xboole_0)
      | r2_hidden(X9,sK1)
      | ~ r2_hidden(X9,sK3) ) ),
    inference(superposition,[],[f68,f12244])).

fof(f12244,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f12241,f35])).

fof(f12241,plain,(
    v1_xboole_0(k4_xboole_0(sK3,sK1)) ),
    inference(duplicate_literal_removal,[],[f12238])).

fof(f12238,plain,
    ( v1_xboole_0(k4_xboole_0(sK3,sK1))
    | v1_xboole_0(k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f12122,f80])).

fof(f12122,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X2,sK1)),sK3)
      | v1_xboole_0(k4_xboole_0(X2,sK1)) ) ),
    inference(resolution,[],[f12108,f36])).

fof(f12108,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k4_xboole_0(X8,sK1))
      | ~ r2_hidden(X9,sK3) ) ),
    inference(subsumption_resolution,[],[f12068,f9653])).

fof(f12068,plain,(
    ! [X8,X9] :
      ( r2_hidden(X9,k1_xboole_0)
      | ~ r2_hidden(X9,k4_xboole_0(X8,sK1))
      | ~ r2_hidden(X9,sK3) ) ),
    inference(superposition,[],[f71,f12059])).

fof(f12059,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X3,sK1)) ),
    inference(subsumption_resolution,[],[f12056,f66])).

fof(f12056,plain,(
    ! [X3] :
      ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
      | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X3,sK1)) ) ),
    inference(superposition,[],[f5012,f750])).

fof(f5012,plain,(
    ! [X16] :
      ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X16))
      | k1_xboole_0 = k3_xboole_0(sK3,X16) ) ),
    inference(subsumption_resolution,[],[f4990,f31])).

fof(f4990,plain,(
    ! [X16] :
      ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X16))
      | k1_xboole_0 = k3_xboole_0(sK3,X16)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f46,f4399])).

fof(f4399,plain,(
    ! [X9] : k2_zfmisc_1(sK0,k3_xboole_0(sK1,X9)) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,X9)) ),
    inference(forward_demodulation,[],[f4383,f224])).

fof(f4383,plain,(
    ! [X9] : k2_zfmisc_1(sK0,k3_xboole_0(sK3,X9)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X9)) ),
    inference(superposition,[],[f224,f4367])).

fof(f4367,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(subsumption_resolution,[],[f4365,f1855])).

fof(f4365,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(resolution,[],[f4348,f41])).

fof(f4348,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f4275,f30])).

fof(f4275,plain,(
    ! [X153] : r1_tarski(k2_zfmisc_1(sK0,X153),k2_zfmisc_1(sK2,X153)) ),
    inference(superposition,[],[f2502,f2730])).

fof(f2730,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f2726,f38])).

fof(f2726,plain,(
    r1_tarski(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f2717])).

fof(f2717,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f2678,f44])).

fof(f2678,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0,sK2),sK0)
      | r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f2672,f45])).

fof(f2672,plain,(
    ! [X17] :
      ( r2_hidden(X17,sK2)
      | ~ r2_hidden(X17,sK0) ) ),
    inference(subsumption_resolution,[],[f2637,f92])).

fof(f2637,plain,(
    ! [X17] :
      ( r2_hidden(X17,k1_xboole_0)
      | r2_hidden(X17,sK2)
      | ~ r2_hidden(X17,sK0) ) ),
    inference(superposition,[],[f68,f2611])).

fof(f2611,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f2605,f32])).

fof(f2605,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f2593])).

fof(f2593,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f46,f2539])).

fof(f2539,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f2466,f210])).

fof(f2466,plain,(
    ! [X11] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(X11,sK2),sK0),sK1) ),
    inference(superposition,[],[f228,f448])).

fof(f448,plain,(
    ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X12,sK2),X13),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f435,f30])).

fof(f435,plain,(
    ! [X4,X2,X5,X3] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X2,X3),X4),k2_zfmisc_1(X3,X5)) ),
    inference(forward_demodulation,[],[f417,f67])).

fof(f417,plain,(
    ! [X4,X2,X5,X3] : k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X2,X3),X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f63,f392])).

fof(f2502,plain,(
    ! [X80,X81,X82] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X80,X82),X81),k2_zfmisc_1(X82,X81)) ),
    inference(superposition,[],[f254,f228])).

fof(f29,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f2729,plain,
    ( ~ r1_tarski(sK2,sK0)
    | sK0 = sK2 ),
    inference(resolution,[],[f2726,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (361)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  % (353)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (353)Refutation not found, incomplete strategy% (353)------------------------------
% 0.21/0.49  % (353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (353)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (353)Memory used [KB]: 10746
% 0.21/0.49  % (353)Time elapsed: 0.064 s
% 0.21/0.49  % (353)------------------------------
% 0.21/0.49  % (353)------------------------------
% 0.21/0.56  % (359)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (367)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (348)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (345)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (347)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (347)Refutation not found, incomplete strategy% (347)------------------------------
% 0.21/0.57  % (347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (347)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (347)Memory used [KB]: 10746
% 0.21/0.57  % (347)Time elapsed: 0.150 s
% 0.21/0.57  % (347)------------------------------
% 0.21/0.57  % (347)------------------------------
% 0.21/0.57  % (367)Refutation not found, incomplete strategy% (367)------------------------------
% 0.21/0.57  % (367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (367)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (367)Memory used [KB]: 10746
% 0.21/0.57  % (367)Time elapsed: 0.106 s
% 0.21/0.57  % (367)------------------------------
% 0.21/0.57  % (367)------------------------------
% 0.21/0.57  % (355)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.58  % (363)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.58  % (351)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % (370)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.59  % (349)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.59  % (371)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.60  % (350)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.60  % (346)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.60  % (356)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.60  % (345)Refutation not found, incomplete strategy% (345)------------------------------
% 0.21/0.60  % (345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (345)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (345)Memory used [KB]: 1663
% 0.21/0.60  % (345)Time elapsed: 0.150 s
% 0.21/0.60  % (345)------------------------------
% 0.21/0.60  % (345)------------------------------
% 0.21/0.60  % (365)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.60  % (360)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.60  % (364)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.61  % (373)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.61  % (362)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.61  % (372)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.61  % (368)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.61  % (358)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.62  % (352)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.86/0.62  % (357)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.86/0.62  % (369)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.86/0.62  % (399)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.86/0.63  % (365)Refutation not found, incomplete strategy% (365)------------------------------
% 1.86/0.63  % (365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.63  % (365)Termination reason: Refutation not found, incomplete strategy
% 1.86/0.63  
% 1.86/0.63  % (365)Memory used [KB]: 10746
% 1.86/0.63  % (365)Time elapsed: 0.201 s
% 1.86/0.63  % (365)------------------------------
% 1.86/0.63  % (365)------------------------------
% 1.86/0.63  % (354)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.86/0.63  % (399)Refutation not found, incomplete strategy% (399)------------------------------
% 1.86/0.63  % (399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.63  % (399)Termination reason: Refutation not found, incomplete strategy
% 1.86/0.63  
% 1.86/0.63  % (399)Memory used [KB]: 6140
% 1.86/0.63  % (399)Time elapsed: 0.006 s
% 1.86/0.63  % (399)------------------------------
% 1.86/0.63  % (399)------------------------------
% 1.86/0.63  % (366)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.86/0.63  % (366)Refutation not found, incomplete strategy% (366)------------------------------
% 1.86/0.63  % (366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.63  % (366)Termination reason: Refutation not found, incomplete strategy
% 1.86/0.63  
% 1.86/0.63  % (366)Memory used [KB]: 1791
% 1.86/0.63  % (366)Time elapsed: 0.210 s
% 1.86/0.63  % (366)------------------------------
% 1.86/0.63  % (366)------------------------------
% 2.16/0.64  % (368)Refutation not found, incomplete strategy% (368)------------------------------
% 2.16/0.64  % (368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.64  % (362)Refutation not found, incomplete strategy% (362)------------------------------
% 2.16/0.64  % (362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.64  % (368)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.64  % (362)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.64  
% 2.16/0.64  
% 2.16/0.64  % (368)Memory used [KB]: 1791
% 2.16/0.64  % (362)Memory used [KB]: 10618
% 2.16/0.64  % (368)Time elapsed: 0.208 s
% 2.16/0.64  % (368)------------------------------
% 2.16/0.64  % (368)------------------------------
% 2.16/0.64  % (362)Time elapsed: 0.203 s
% 2.16/0.64  % (362)------------------------------
% 2.16/0.64  % (362)------------------------------
% 2.16/0.64  % (374)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.95/0.77  % (404)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.95/0.77  % (400)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.95/0.81  % (401)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.95/0.84  % (402)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.95/0.84  % (350)Time limit reached!
% 2.95/0.84  % (350)------------------------------
% 2.95/0.84  % (350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.84  % (350)Termination reason: Time limit
% 2.95/0.84  
% 2.95/0.84  % (350)Memory used [KB]: 7291
% 2.95/0.84  % (350)Time elapsed: 0.406 s
% 2.95/0.84  % (350)------------------------------
% 2.95/0.84  % (350)------------------------------
% 3.50/0.86  % (405)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 3.50/0.88  % (403)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.71/0.89  % (406)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.71/0.90  % (407)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.71/0.93  % (355)Time limit reached!
% 3.71/0.93  % (355)------------------------------
% 3.71/0.93  % (355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.71/0.93  % (355)Termination reason: Time limit
% 3.71/0.93  % (355)Termination phase: Saturation
% 3.71/0.93  
% 3.71/0.93  % (355)Memory used [KB]: 15863
% 3.71/0.93  % (355)Time elapsed: 0.500 s
% 3.71/0.93  % (355)------------------------------
% 3.71/0.93  % (355)------------------------------
% 3.71/0.93  % (346)Time limit reached!
% 3.71/0.93  % (346)------------------------------
% 3.71/0.93  % (346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.71/0.93  % (346)Termination reason: Time limit
% 3.71/0.93  % (346)Termination phase: Saturation
% 3.71/0.93  
% 3.71/0.93  % (346)Memory used [KB]: 6908
% 3.71/0.93  % (346)Time elapsed: 0.500 s
% 3.71/0.93  % (346)------------------------------
% 3.71/0.93  % (346)------------------------------
% 4.08/0.96  % (357)Time limit reached!
% 4.08/0.96  % (357)------------------------------
% 4.08/0.96  % (357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/0.98  % (357)Termination reason: Time limit
% 4.08/0.98  
% 4.08/0.98  % (357)Memory used [KB]: 8187
% 4.08/0.98  % (357)Time elapsed: 0.530 s
% 4.08/0.98  % (357)------------------------------
% 4.08/0.98  % (357)------------------------------
% 4.41/1.03  % (410)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.41/1.03  % (352)Time limit reached!
% 4.41/1.03  % (352)------------------------------
% 4.41/1.03  % (352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/1.03  % (361)Time limit reached!
% 4.41/1.03  % (361)------------------------------
% 4.41/1.03  % (361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/1.04  % (373)Time limit reached!
% 4.41/1.04  % (373)------------------------------
% 4.41/1.04  % (373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/1.04  % (373)Termination reason: Time limit
% 4.41/1.04  % (373)Termination phase: Saturation
% 4.41/1.04  
% 4.41/1.04  % (373)Memory used [KB]: 7931
% 4.41/1.04  % (373)Time elapsed: 0.600 s
% 4.41/1.04  % (373)------------------------------
% 4.41/1.04  % (373)------------------------------
% 4.41/1.05  % (352)Termination reason: Time limit
% 4.41/1.05  % (352)Termination phase: Saturation
% 4.41/1.05  
% 4.41/1.05  % (352)Memory used [KB]: 11385
% 4.41/1.05  % (352)Time elapsed: 0.600 s
% 4.41/1.05  % (352)------------------------------
% 4.41/1.05  % (352)------------------------------
% 4.41/1.05  % (361)Termination reason: Time limit
% 4.41/1.05  
% 4.41/1.05  % (361)Memory used [KB]: 18166
% 4.41/1.05  % (361)Time elapsed: 0.618 s
% 4.41/1.05  % (361)------------------------------
% 4.41/1.05  % (361)------------------------------
% 4.41/1.06  % (411)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.71/1.06  % (411)Refutation not found, incomplete strategy% (411)------------------------------
% 4.71/1.06  % (411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.71/1.06  % (411)Termination reason: Refutation not found, incomplete strategy
% 4.71/1.06  
% 4.71/1.06  % (411)Memory used [KB]: 6268
% 4.71/1.06  % (411)Time elapsed: 0.104 s
% 4.71/1.06  % (411)------------------------------
% 4.71/1.06  % (411)------------------------------
% 4.71/1.07  % (402)Time limit reached!
% 4.71/1.07  % (402)------------------------------
% 4.71/1.07  % (402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.71/1.07  % (402)Termination reason: Time limit
% 4.71/1.07  % (402)Termination phase: Saturation
% 4.71/1.07  
% 4.71/1.07  % (402)Memory used [KB]: 7547
% 4.71/1.07  % (402)Time elapsed: 0.400 s
% 4.71/1.07  % (402)------------------------------
% 4.71/1.07  % (402)------------------------------
% 4.71/1.08  % (413)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 4.71/1.08  % (412)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.71/1.09  % (412)Refutation not found, incomplete strategy% (412)------------------------------
% 4.71/1.09  % (412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.71/1.09  % (412)Termination reason: Refutation not found, incomplete strategy
% 4.71/1.09  
% 4.71/1.09  % (412)Memory used [KB]: 1791
% 4.71/1.09  % (412)Time elapsed: 0.109 s
% 4.71/1.09  % (412)------------------------------
% 4.71/1.09  % (412)------------------------------
% 4.71/1.10  % (403)Time limit reached!
% 4.71/1.10  % (403)------------------------------
% 4.71/1.10  % (403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.71/1.10  % (403)Termination reason: Time limit
% 4.71/1.10  
% 4.71/1.10  % (403)Memory used [KB]: 12537
% 4.71/1.10  % (403)Time elapsed: 0.408 s
% 4.71/1.10  % (403)------------------------------
% 4.71/1.10  % (403)------------------------------
% 6.25/1.16  % (444)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.25/1.16  % (437)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.25/1.18  % (440)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.25/1.19  % (440)Refutation not found, incomplete strategy% (440)------------------------------
% 6.25/1.19  % (440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.25/1.19  % (440)Termination reason: Refutation not found, incomplete strategy
% 6.25/1.19  
% 6.25/1.19  % (440)Memory used [KB]: 6268
% 6.25/1.19  % (440)Time elapsed: 0.105 s
% 6.25/1.19  % (440)------------------------------
% 6.25/1.19  % (440)------------------------------
% 6.25/1.19  % (441)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.25/1.19  % (433)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.25/1.19  % (433)Refutation not found, incomplete strategy% (433)------------------------------
% 6.25/1.19  % (433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.25/1.19  % (433)Termination reason: Refutation not found, incomplete strategy
% 6.25/1.19  
% 6.25/1.19  % (433)Memory used [KB]: 1663
% 6.25/1.19  % (433)Time elapsed: 0.116 s
% 6.25/1.19  % (433)------------------------------
% 6.25/1.19  % (433)------------------------------
% 6.58/1.21  % (455)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.58/1.22  % (461)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 7.38/1.31  % (520)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 7.38/1.32  % (527)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.46/1.49  % (441)Time limit reached!
% 8.46/1.49  % (441)------------------------------
% 8.46/1.49  % (441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.46/1.49  % (441)Termination reason: Time limit
% 8.46/1.49  
% 8.46/1.49  % (441)Memory used [KB]: 4349
% 8.46/1.49  % (441)Time elapsed: 0.410 s
% 8.46/1.49  % (441)------------------------------
% 8.46/1.49  % (441)------------------------------
% 8.78/1.52  % (413)Time limit reached!
% 8.78/1.52  % (413)------------------------------
% 8.78/1.52  % (413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.78/1.52  % (413)Termination reason: Time limit
% 8.78/1.52  
% 8.78/1.52  % (413)Memory used [KB]: 3837
% 8.78/1.52  % (413)Time elapsed: 0.517 s
% 8.78/1.52  % (413)------------------------------
% 8.78/1.52  % (413)------------------------------
% 8.78/1.53  % (461)Time limit reached!
% 8.78/1.53  % (461)------------------------------
% 8.78/1.53  % (461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.78/1.54  % (461)Termination reason: Time limit
% 8.78/1.54  % (461)Termination phase: Saturation
% 8.78/1.54  
% 8.78/1.54  % (461)Memory used [KB]: 2686
% 8.78/1.54  % (461)Time elapsed: 0.400 s
% 8.78/1.54  % (461)------------------------------
% 8.78/1.54  % (461)------------------------------
% 9.53/1.63  % (637)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 9.53/1.65  % (371)Time limit reached!
% 9.53/1.65  % (371)------------------------------
% 9.53/1.65  % (371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.53/1.65  % (371)Termination reason: Time limit
% 9.53/1.65  
% 9.53/1.65  % (371)Memory used [KB]: 24434
% 9.53/1.65  % (371)Time elapsed: 1.216 s
% 9.53/1.65  % (371)------------------------------
% 9.53/1.65  % (371)------------------------------
% 9.53/1.65  % (659)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 10.25/1.66  % (674)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 10.25/1.72  % (360)Time limit reached!
% 10.25/1.72  % (360)------------------------------
% 10.25/1.72  % (360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.25/1.74  % (360)Termination reason: Time limit
% 10.25/1.74  % (360)Termination phase: Saturation
% 10.25/1.74  
% 10.25/1.74  % (360)Memory used [KB]: 17910
% 10.25/1.74  % (360)Time elapsed: 1.300 s
% 10.25/1.74  % (360)------------------------------
% 10.25/1.74  % (360)------------------------------
% 11.06/1.77  % (369)Time limit reached!
% 11.06/1.77  % (369)------------------------------
% 11.06/1.77  % (369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.06/1.79  % (369)Termination reason: Time limit
% 11.06/1.79  % (369)Termination phase: Saturation
% 11.06/1.79  
% 11.06/1.79  % (369)Memory used [KB]: 19957
% 11.06/1.79  % (369)Time elapsed: 1.300 s
% 11.06/1.79  % (369)------------------------------
% 11.06/1.79  % (369)------------------------------
% 11.06/1.79  % (694)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 11.42/1.81  % (694)Refutation not found, incomplete strategy% (694)------------------------------
% 11.42/1.81  % (694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.42/1.81  % (694)Termination reason: Refutation not found, incomplete strategy
% 11.42/1.81  
% 11.42/1.81  % (694)Memory used [KB]: 6268
% 11.42/1.81  % (694)Time elapsed: 0.093 s
% 11.42/1.81  % (694)------------------------------
% 11.42/1.81  % (694)------------------------------
% 11.74/1.88  % (695)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.74/1.92  % (349)Time limit reached!
% 11.74/1.92  % (349)------------------------------
% 11.74/1.92  % (349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.74/1.92  % (349)Termination reason: Time limit
% 11.74/1.92  % (349)Termination phase: Saturation
% 11.74/1.92  
% 11.74/1.92  % (349)Memory used [KB]: 21748
% 11.74/1.92  % (349)Time elapsed: 1.500 s
% 11.74/1.92  % (349)------------------------------
% 11.74/1.92  % (349)------------------------------
% 11.74/1.92  % (696)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 12.46/1.95  % (372)Time limit reached!
% 12.46/1.95  % (372)------------------------------
% 12.46/1.95  % (372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.46/1.95  % (372)Termination reason: Time limit
% 12.46/1.95  % (372)Termination phase: Saturation
% 12.46/1.95  
% 12.46/1.95  % (372)Memory used [KB]: 15991
% 12.46/1.95  % (372)Time elapsed: 1.500 s
% 12.46/1.95  % (372)------------------------------
% 12.46/1.95  % (372)------------------------------
% 12.46/1.95  % (696)Refutation not found, incomplete strategy% (696)------------------------------
% 12.46/1.95  % (696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.46/1.95  % (696)Termination reason: Refutation not found, incomplete strategy
% 12.46/1.95  
% 12.46/1.95  % (696)Memory used [KB]: 10746
% 12.46/1.95  % (696)Time elapsed: 0.125 s
% 12.46/1.95  % (696)------------------------------
% 12.46/1.95  % (696)------------------------------
% 12.46/1.95  % (405)Time limit reached!
% 12.46/1.95  % (405)------------------------------
% 12.46/1.95  % (405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.46/1.95  % (405)Termination reason: Time limit
% 12.46/1.95  % (405)Termination phase: Saturation
% 12.46/1.95  
% 12.46/1.95  % (405)Memory used [KB]: 13944
% 12.46/1.95  % (405)Time elapsed: 1.200 s
% 12.46/1.95  % (405)------------------------------
% 12.46/1.95  % (405)------------------------------
% 12.46/1.98  % (674)Time limit reached!
% 12.46/1.98  % (674)------------------------------
% 12.46/1.98  % (674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.46/1.98  % (674)Termination reason: Time limit
% 12.46/1.98  % (674)Termination phase: Saturation
% 12.46/1.98  
% 12.46/1.98  % (674)Memory used [KB]: 11257
% 12.46/1.98  % (674)Time elapsed: 0.400 s
% 12.46/1.98  % (674)------------------------------
% 12.46/1.98  % (674)------------------------------
% 13.42/2.08  % (356)Time limit reached!
% 13.42/2.08  % (356)------------------------------
% 13.42/2.08  % (356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.42/2.10  % (356)Termination reason: Time limit
% 13.42/2.10  
% 13.42/2.10  % (356)Memory used [KB]: 33517
% 13.42/2.10  % (356)Time elapsed: 1.638 s
% 13.42/2.10  % (356)------------------------------
% 13.42/2.10  % (356)------------------------------
% 14.10/2.19  % (695)Time limit reached!
% 14.10/2.19  % (695)------------------------------
% 14.10/2.19  % (695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.10/2.19  % (695)Termination reason: Time limit
% 14.10/2.19  % (695)Termination phase: Saturation
% 14.10/2.19  
% 14.10/2.19  % (695)Memory used [KB]: 12153
% 14.10/2.19  % (695)Time elapsed: 0.400 s
% 14.10/2.19  % (695)------------------------------
% 14.10/2.19  % (695)------------------------------
% 15.38/2.32  % (359)Time limit reached!
% 15.38/2.32  % (359)------------------------------
% 15.38/2.32  % (359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.38/2.32  % (359)Termination reason: Time limit
% 15.38/2.32  % (359)Termination phase: Saturation
% 15.38/2.32  
% 15.38/2.32  % (359)Memory used [KB]: 5884
% 15.38/2.32  % (359)Time elapsed: 1.827 s
% 15.38/2.32  % (359)------------------------------
% 15.38/2.32  % (359)------------------------------
% 15.38/2.34  % (401)Time limit reached!
% 15.38/2.34  % (401)------------------------------
% 15.38/2.34  % (401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.38/2.34  % (401)Termination reason: Time limit
% 15.38/2.34  % (401)Termination phase: Saturation
% 15.38/2.34  
% 15.38/2.34  % (401)Memory used [KB]: 19573
% 15.38/2.34  % (401)Time elapsed: 1.700 s
% 15.38/2.34  % (401)------------------------------
% 15.38/2.34  % (401)------------------------------
% 16.28/2.42  % (455)Time limit reached!
% 16.28/2.42  % (455)------------------------------
% 16.28/2.42  % (455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.28/2.42  % (455)Termination reason: Time limit
% 16.28/2.42  % (455)Termination phase: Saturation
% 16.28/2.42  
% 16.28/2.42  % (455)Memory used [KB]: 10106
% 16.28/2.42  % (455)Time elapsed: 1.300 s
% 16.28/2.42  % (455)------------------------------
% 16.28/2.42  % (455)------------------------------
% 16.28/2.43  % (407)Time limit reached!
% 16.28/2.43  % (407)------------------------------
% 16.28/2.43  % (407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.28/2.43  % (407)Termination reason: Time limit
% 16.28/2.43  % (407)Termination phase: Saturation
% 16.28/2.43  
% 16.28/2.43  % (407)Memory used [KB]: 21236
% 16.28/2.43  % (407)Time elapsed: 1.700 s
% 16.28/2.43  % (407)------------------------------
% 16.28/2.43  % (407)------------------------------
% 16.52/2.46  % (351)Refutation found. Thanks to Tanya!
% 16.52/2.46  % SZS status Theorem for theBenchmark
% 16.52/2.46  % SZS output start Proof for theBenchmark
% 16.52/2.46  % (363)Time limit reached!
% 16.52/2.46  % (363)------------------------------
% 16.52/2.46  % (363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.52/2.46  % (363)Termination reason: Time limit
% 16.52/2.46  
% 16.52/2.46  % (363)Memory used [KB]: 13048
% 16.52/2.46  % (363)Time elapsed: 2.050 s
% 16.52/2.46  % (363)------------------------------
% 16.52/2.46  % (363)------------------------------
% 16.52/2.47  fof(f19841,plain,(
% 16.52/2.47    $false),
% 16.52/2.47    inference(global_subsumption,[],[f2729,f16749,f19838])).
% 16.52/2.47  fof(f19838,plain,(
% 16.52/2.47    r1_tarski(sK2,sK0)),
% 16.52/2.47    inference(duplicate_literal_removal,[],[f19830])).
% 16.52/2.47  fof(f19830,plain,(
% 16.52/2.47    r1_tarski(sK2,sK0) | r1_tarski(sK2,sK0)),
% 16.52/2.47    inference(resolution,[],[f19514,f45])).
% 16.52/2.47  fof(f45,plain,(
% 16.52/2.47    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 16.52/2.47    inference(cnf_transformation,[],[f27])).
% 16.52/2.47  fof(f27,plain,(
% 16.52/2.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 16.52/2.47    inference(ennf_transformation,[],[f2])).
% 16.52/2.47  fof(f2,axiom,(
% 16.52/2.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 16.52/2.47  fof(f19514,plain,(
% 16.52/2.47    ( ! [X18] : (r2_hidden(sK5(sK2,X18),sK0) | r1_tarski(sK2,X18)) )),
% 16.52/2.47    inference(resolution,[],[f19482,f44])).
% 16.52/2.47  fof(f44,plain,(
% 16.52/2.47    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 16.52/2.47    inference(cnf_transformation,[],[f27])).
% 16.52/2.47  fof(f19482,plain,(
% 16.52/2.47    ( ! [X16] : (~r2_hidden(X16,sK2) | r2_hidden(X16,sK0)) )),
% 16.52/2.47    inference(subsumption_resolution,[],[f19437,f9653])).
% 16.52/2.47  fof(f9653,plain,(
% 16.52/2.47    ( ! [X8] : (~r2_hidden(X8,k1_xboole_0)) )),
% 16.52/2.47    inference(subsumption_resolution,[],[f9646,f92])).
% 16.52/2.47  fof(f92,plain,(
% 16.52/2.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 16.52/2.47    inference(superposition,[],[f73,f34])).
% 16.52/2.47  fof(f34,plain,(
% 16.52/2.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 16.52/2.47    inference(cnf_transformation,[],[f11])).
% 16.52/2.47  fof(f11,axiom,(
% 16.52/2.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 16.52/2.47  fof(f73,plain,(
% 16.52/2.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 16.52/2.47    inference(equality_resolution,[],[f60])).
% 16.52/2.47  fof(f60,plain,(
% 16.52/2.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 16.52/2.47    inference(cnf_transformation,[],[f3])).
% 16.52/2.47  fof(f3,axiom,(
% 16.52/2.47    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 16.52/2.47  fof(f9646,plain,(
% 16.52/2.47    ( ! [X8,X9] : (~r2_hidden(X8,k1_xboole_0) | ~r2_hidden(X8,k4_xboole_0(X9,k2_zfmisc_1(k1_xboole_0,sK3)))) )),
% 16.52/2.47    inference(superposition,[],[f2036,f67])).
% 16.52/2.47  fof(f67,plain,(
% 16.52/2.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 16.52/2.47    inference(equality_resolution,[],[f47])).
% 16.52/2.47  fof(f47,plain,(
% 16.52/2.47    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 16.52/2.47    inference(cnf_transformation,[],[f13])).
% 16.52/2.47  fof(f13,axiom,(
% 16.52/2.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 16.52/2.47  fof(f2036,plain,(
% 16.52/2.47    ( ! [X14,X15,X13] : (~r2_hidden(X13,k2_zfmisc_1(X14,sK1)) | ~r2_hidden(X13,k4_xboole_0(X15,k2_zfmisc_1(X14,sK3)))) )),
% 16.52/2.47    inference(resolution,[],[f1893,f69])).
% 16.52/2.47  fof(f69,plain,(
% 16.52/2.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 16.52/2.47    inference(equality_resolution,[],[f55])).
% 16.52/2.47  fof(f55,plain,(
% 16.52/2.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 16.52/2.47    inference(cnf_transformation,[],[f4])).
% 16.52/2.47  fof(f4,axiom,(
% 16.52/2.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 16.52/2.47  fof(f1893,plain,(
% 16.52/2.47    ( ! [X2,X1] : (r2_hidden(X1,k2_zfmisc_1(X2,sK3)) | ~r2_hidden(X1,k2_zfmisc_1(X2,sK1))) )),
% 16.52/2.47    inference(resolution,[],[f1855,f43])).
% 16.52/2.47  fof(f43,plain,(
% 16.52/2.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 16.52/2.47    inference(cnf_transformation,[],[f27])).
% 16.52/2.47  fof(f1855,plain,(
% 16.52/2.47    ( ! [X121] : (r1_tarski(k2_zfmisc_1(X121,sK1),k2_zfmisc_1(X121,sK3))) )),
% 16.52/2.47    inference(superposition,[],[f1160,f1328])).
% 16.52/2.47  fof(f1328,plain,(
% 16.52/2.47    sK1 = k3_xboole_0(sK1,sK3)),
% 16.52/2.47    inference(resolution,[],[f1324,f38])).
% 16.52/2.47  fof(f38,plain,(
% 16.52/2.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 16.52/2.47    inference(cnf_transformation,[],[f24])).
% 16.52/2.47  fof(f24,plain,(
% 16.52/2.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 16.52/2.47    inference(ennf_transformation,[],[f10])).
% 16.52/2.47  fof(f10,axiom,(
% 16.52/2.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 16.52/2.47  fof(f1324,plain,(
% 16.52/2.47    r1_tarski(sK1,sK3)),
% 16.52/2.47    inference(duplicate_literal_removal,[],[f1315])).
% 16.52/2.47  fof(f1315,plain,(
% 16.52/2.47    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3)),
% 16.52/2.47    inference(resolution,[],[f1284,f44])).
% 16.52/2.47  fof(f1284,plain,(
% 16.52/2.47    ( ! [X0] : (~r2_hidden(sK5(X0,sK3),sK1) | r1_tarski(X0,sK3)) )),
% 16.52/2.47    inference(resolution,[],[f1279,f45])).
% 16.52/2.47  fof(f1279,plain,(
% 16.52/2.47    ( ! [X17] : (r2_hidden(X17,sK3) | ~r2_hidden(X17,sK1)) )),
% 16.52/2.47    inference(subsumption_resolution,[],[f1245,f92])).
% 16.52/2.47  fof(f1245,plain,(
% 16.52/2.47    ( ! [X17] : (r2_hidden(X17,k1_xboole_0) | r2_hidden(X17,sK3) | ~r2_hidden(X17,sK1)) )),
% 16.52/2.47    inference(superposition,[],[f68,f1229])).
% 16.52/2.47  fof(f1229,plain,(
% 16.52/2.47    k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 16.52/2.47    inference(subsumption_resolution,[],[f1224,f31])).
% 16.52/2.47  fof(f31,plain,(
% 16.52/2.47    k1_xboole_0 != sK0),
% 16.52/2.47    inference(cnf_transformation,[],[f21])).
% 16.52/2.47  fof(f21,plain,(
% 16.52/2.47    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 16.52/2.47    inference(flattening,[],[f20])).
% 16.52/2.47  fof(f20,plain,(
% 16.52/2.47    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 16.52/2.47    inference(ennf_transformation,[],[f16])).
% 16.52/2.47  fof(f16,negated_conjecture,(
% 16.52/2.47    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 16.52/2.47    inference(negated_conjecture,[],[f15])).
% 16.52/2.47  fof(f15,conjecture,(
% 16.52/2.47    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 16.52/2.47  fof(f1224,plain,(
% 16.52/2.47    k1_xboole_0 = k4_xboole_0(sK1,sK3) | k1_xboole_0 = sK0),
% 16.52/2.47    inference(trivial_inequality_removal,[],[f1217])).
% 16.52/2.47  fof(f1217,plain,(
% 16.52/2.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK1,sK3) | k1_xboole_0 = sK0),
% 16.52/2.47    inference(superposition,[],[f46,f1188])).
% 16.52/2.47  fof(f1188,plain,(
% 16.52/2.47    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 16.52/2.47    inference(superposition,[],[f1130,f210])).
% 16.52/2.47  fof(f210,plain,(
% 16.52/2.47    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k3_xboole_0(k4_xboole_0(X7,X8),X7)) )),
% 16.52/2.47    inference(resolution,[],[f204,f38])).
% 16.52/2.47  fof(f204,plain,(
% 16.52/2.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 16.52/2.47    inference(duplicate_literal_removal,[],[f195])).
% 16.52/2.47  fof(f195,plain,(
% 16.52/2.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0) | r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 16.52/2.47    inference(resolution,[],[f81,f45])).
% 16.52/2.47  fof(f81,plain,(
% 16.52/2.47    ( ! [X4,X2,X3] : (r2_hidden(sK5(k4_xboole_0(X2,X3),X4),X2) | r1_tarski(k4_xboole_0(X2,X3),X4)) )),
% 16.52/2.47    inference(resolution,[],[f70,f44])).
% 16.52/2.47  fof(f70,plain,(
% 16.52/2.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 16.52/2.47    inference(equality_resolution,[],[f54])).
% 16.52/2.47  fof(f54,plain,(
% 16.52/2.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 16.52/2.47    inference(cnf_transformation,[],[f4])).
% 16.52/2.47  fof(f1130,plain,(
% 16.52/2.47    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X3,sK3),sK1))) )),
% 16.52/2.47    inference(superposition,[],[f224,f502])).
% 16.52/2.47  fof(f502,plain,(
% 16.52/2.47    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X13,sK3)),k2_zfmisc_1(sK0,sK1))) )),
% 16.52/2.47    inference(superposition,[],[f436,f30])).
% 16.52/2.47  fof(f30,plain,(
% 16.52/2.47    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 16.52/2.47    inference(cnf_transformation,[],[f21])).
% 16.52/2.47  fof(f436,plain,(
% 16.52/2.47    ( ! [X6,X8,X7,X9] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X8,k4_xboole_0(X6,X7)),k2_zfmisc_1(X9,X7))) )),
% 16.52/2.47    inference(forward_demodulation,[],[f418,f66])).
% 16.52/2.47  fof(f66,plain,(
% 16.52/2.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 16.52/2.47    inference(equality_resolution,[],[f48])).
% 16.52/2.47  fof(f48,plain,(
% 16.52/2.47    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 16.52/2.47    inference(cnf_transformation,[],[f13])).
% 16.52/2.47  fof(f418,plain,(
% 16.52/2.47    ( ! [X6,X8,X7,X9] : (k3_xboole_0(k2_zfmisc_1(X8,k4_xboole_0(X6,X7)),k2_zfmisc_1(X9,X7)) = k2_zfmisc_1(k3_xboole_0(X8,X9),k1_xboole_0)) )),
% 16.52/2.47    inference(superposition,[],[f63,f392])).
% 16.52/2.47  fof(f392,plain,(
% 16.52/2.47    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 16.52/2.47    inference(resolution,[],[f391,f35])).
% 16.52/2.47  fof(f35,plain,(
% 16.52/2.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 16.52/2.47    inference(cnf_transformation,[],[f22])).
% 16.52/2.47  fof(f22,plain,(
% 16.52/2.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 16.52/2.47    inference(ennf_transformation,[],[f7])).
% 16.52/2.47  fof(f7,axiom,(
% 16.52/2.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 16.52/2.47  fof(f391,plain,(
% 16.52/2.47    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))) )),
% 16.52/2.47    inference(duplicate_literal_removal,[],[f382])).
% 16.52/2.47  fof(f382,plain,(
% 16.52/2.47    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) | v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))) )),
% 16.52/2.47    inference(resolution,[],[f153,f89])).
% 16.52/2.47  fof(f89,plain,(
% 16.52/2.47    ( ! [X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1)),X0) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 16.52/2.47    inference(resolution,[],[f73,f36])).
% 16.52/2.47  fof(f36,plain,(
% 16.52/2.47    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 16.52/2.47    inference(cnf_transformation,[],[f23])).
% 16.52/2.47  fof(f23,plain,(
% 16.52/2.47    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 16.52/2.47    inference(ennf_transformation,[],[f19])).
% 16.52/2.47  fof(f19,plain,(
% 16.52/2.47    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 16.52/2.47    inference(unused_predicate_definition_removal,[],[f1])).
% 16.52/2.47  fof(f1,axiom,(
% 16.52/2.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 16.52/2.47  fof(f153,plain,(
% 16.52/2.47    ( ! [X2,X0,X1] : (~r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X1)) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 16.52/2.47    inference(resolution,[],[f84,f69])).
% 16.52/2.47  fof(f84,plain,(
% 16.52/2.47    ( ! [X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1)),X1) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 16.52/2.47    inference(resolution,[],[f72,f36])).
% 16.52/2.47  fof(f72,plain,(
% 16.52/2.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X1)) )),
% 16.52/2.47    inference(equality_resolution,[],[f61])).
% 16.52/2.47  fof(f61,plain,(
% 16.52/2.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 16.52/2.47    inference(cnf_transformation,[],[f3])).
% 16.52/2.47  fof(f63,plain,(
% 16.52/2.47    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 16.52/2.47    inference(cnf_transformation,[],[f14])).
% 16.52/2.47  fof(f14,axiom,(
% 16.52/2.47    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 16.52/2.47  fof(f224,plain,(
% 16.52/2.47    ( ! [X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(X3,k3_xboole_0(X4,X5))) )),
% 16.52/2.47    inference(superposition,[],[f63,f37])).
% 16.52/2.47  fof(f37,plain,(
% 16.52/2.47    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 16.52/2.47    inference(cnf_transformation,[],[f17])).
% 16.52/2.47  fof(f17,plain,(
% 16.52/2.47    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 16.52/2.47    inference(rectify,[],[f6])).
% 16.52/2.47  fof(f6,axiom,(
% 16.52/2.47    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 16.52/2.47  fof(f46,plain,(
% 16.52/2.47    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 16.52/2.47    inference(cnf_transformation,[],[f13])).
% 16.52/2.47  fof(f68,plain,(
% 16.52/2.47    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 16.52/2.47    inference(equality_resolution,[],[f56])).
% 16.52/2.47  fof(f56,plain,(
% 16.52/2.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 16.52/2.47    inference(cnf_transformation,[],[f4])).
% 16.52/2.47  fof(f1160,plain,(
% 16.52/2.47    ( ! [X76,X74,X75] : (r1_tarski(k2_zfmisc_1(X74,k3_xboole_0(X75,X76)),k2_zfmisc_1(X74,X76))) )),
% 16.52/2.47    inference(superposition,[],[f254,f224])).
% 16.52/2.47  fof(f254,plain,(
% 16.52/2.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 16.52/2.47    inference(duplicate_literal_removal,[],[f242])).
% 16.52/2.47  fof(f242,plain,(
% 16.52/2.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 16.52/2.47    inference(resolution,[],[f85,f45])).
% 16.52/2.47  fof(f85,plain,(
% 16.52/2.47    ( ! [X4,X2,X3] : (r2_hidden(sK5(k3_xboole_0(X2,X3),X4),X3) | r1_tarski(k3_xboole_0(X2,X3),X4)) )),
% 16.52/2.47    inference(resolution,[],[f72,f44])).
% 16.52/2.47  fof(f19437,plain,(
% 16.52/2.47    ( ! [X16] : (r2_hidden(X16,k1_xboole_0) | r2_hidden(X16,sK0) | ~r2_hidden(X16,sK2)) )),
% 16.52/2.47    inference(superposition,[],[f68,f19414])).
% 16.52/2.47  fof(f19414,plain,(
% 16.52/2.47    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 16.52/2.47    inference(resolution,[],[f19411,f35])).
% 16.52/2.47  fof(f19411,plain,(
% 16.52/2.47    v1_xboole_0(k4_xboole_0(sK2,sK0))),
% 16.52/2.47    inference(duplicate_literal_removal,[],[f19408])).
% 16.52/2.47  fof(f19408,plain,(
% 16.52/2.47    v1_xboole_0(k4_xboole_0(sK2,sK0)) | v1_xboole_0(k4_xboole_0(sK2,sK0))),
% 16.52/2.47    inference(resolution,[],[f19269,f80])).
% 16.52/2.47  fof(f80,plain,(
% 16.52/2.47    ( ! [X0,X1] : (r2_hidden(sK4(k4_xboole_0(X0,X1)),X0) | v1_xboole_0(k4_xboole_0(X0,X1))) )),
% 16.52/2.47    inference(resolution,[],[f70,f36])).
% 16.52/2.47  fof(f19269,plain,(
% 16.52/2.47    ( ! [X2] : (~r2_hidden(sK4(k4_xboole_0(X2,sK0)),sK2) | v1_xboole_0(k4_xboole_0(X2,sK0))) )),
% 16.52/2.47    inference(resolution,[],[f19251,f36])).
% 16.52/2.47  fof(f19251,plain,(
% 16.52/2.47    ( ! [X8,X7] : (~r2_hidden(X8,k4_xboole_0(X7,sK0)) | ~r2_hidden(X8,sK2)) )),
% 16.52/2.47    inference(subsumption_resolution,[],[f19205,f9653])).
% 16.52/2.47  fof(f19205,plain,(
% 16.52/2.47    ( ! [X8,X7] : (r2_hidden(X8,k1_xboole_0) | ~r2_hidden(X8,k4_xboole_0(X7,sK0)) | ~r2_hidden(X8,sK2)) )),
% 16.52/2.47    inference(superposition,[],[f71,f19198])).
% 16.52/2.47  fof(f19198,plain,(
% 16.52/2.47    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X4,sK0))) )),
% 16.52/2.47    inference(subsumption_resolution,[],[f19196,f67])).
% 16.52/2.47  fof(f19196,plain,(
% 16.52/2.47    ( ! [X4] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X4,sK0))) )),
% 16.52/2.47    inference(superposition,[],[f4116,f750])).
% 16.52/2.47  fof(f750,plain,(
% 16.52/2.47    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 16.52/2.47    inference(resolution,[],[f749,f35])).
% 16.52/2.47  fof(f749,plain,(
% 16.52/2.47    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 16.52/2.47    inference(duplicate_literal_removal,[],[f731])).
% 16.52/2.47  fof(f731,plain,(
% 16.52/2.47    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3))) | v1_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 16.52/2.47    inference(resolution,[],[f165,f84])).
% 16.52/2.47  fof(f165,plain,(
% 16.52/2.47    ( ! [X2,X0,X1] : (~r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X0)) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 16.52/2.47    inference(resolution,[],[f89,f69])).
% 16.52/2.47  fof(f4116,plain,(
% 16.52/2.47    ( ! [X11] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X11),sK1) | k1_xboole_0 = k3_xboole_0(sK2,X11)) )),
% 16.52/2.47    inference(subsumption_resolution,[],[f4098,f32])).
% 16.52/2.47  fof(f32,plain,(
% 16.52/2.47    k1_xboole_0 != sK1),
% 16.52/2.47    inference(cnf_transformation,[],[f21])).
% 16.52/2.47  fof(f4098,plain,(
% 16.52/2.47    ( ! [X11] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,X11),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = k3_xboole_0(sK2,X11)) )),
% 16.52/2.47    inference(superposition,[],[f46,f3466])).
% 16.52/2.47  fof(f3466,plain,(
% 16.52/2.47    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(sK2,X7),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,X7),sK1)) )),
% 16.52/2.47    inference(forward_demodulation,[],[f3393,f228])).
% 16.52/2.47  fof(f228,plain,(
% 16.52/2.47    ( ! [X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X4,X3),k2_zfmisc_1(X5,X3)) = k2_zfmisc_1(k3_xboole_0(X4,X5),X3)) )),
% 16.52/2.47    inference(superposition,[],[f63,f37])).
% 16.52/2.47  fof(f3393,plain,(
% 16.52/2.47    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(sK2,X7),sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X7,sK1))) )),
% 16.52/2.47    inference(superposition,[],[f228,f3310])).
% 16.52/2.47  fof(f3310,plain,(
% 16.52/2.47    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 16.52/2.47    inference(global_subsumption,[],[f1902,f3302])).
% 16.52/2.47  fof(f3302,plain,(
% 16.52/2.47    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 16.52/2.47    inference(forward_demodulation,[],[f3292,f30])).
% 16.52/2.47  fof(f3292,plain,(
% 16.52/2.47    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1))),
% 16.52/2.47    inference(superposition,[],[f3286,f37])).
% 16.52/2.47  fof(f3286,plain,(
% 16.52/2.47    ( ! [X17] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X17,sK3)),k2_zfmisc_1(sK2,sK1))) )),
% 16.52/2.47    inference(forward_demodulation,[],[f3285,f1128])).
% 16.52/2.47  fof(f1128,plain,(
% 16.52/2.47    ( ! [X9] : (k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1))) )),
% 16.52/2.47    inference(superposition,[],[f224,f30])).
% 16.52/2.47  fof(f3285,plain,(
% 16.52/2.47    ( ! [X17] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK2,X17),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK1))) )),
% 16.52/2.47    inference(forward_demodulation,[],[f3271,f63])).
% 16.52/2.47  fof(f3271,plain,(
% 16.52/2.47    ( ! [X17] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,sK0),k3_xboole_0(X17,sK1)),k2_zfmisc_1(sK2,sK1))) )),
% 16.52/2.47    inference(superposition,[],[f1160,f2474])).
% 16.52/2.47  fof(f2474,plain,(
% 16.52/2.47    k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1)),
% 16.52/2.47    inference(superposition,[],[f228,f1903])).
% 16.52/2.47  fof(f1903,plain,(
% 16.52/2.47    k2_zfmisc_1(sK2,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1))),
% 16.52/2.47    inference(resolution,[],[f1898,f38])).
% 16.52/2.47  fof(f1898,plain,(
% 16.52/2.47    r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1))),
% 16.52/2.47    inference(superposition,[],[f1855,f30])).
% 16.52/2.47  fof(f1902,plain,(
% 16.52/2.47    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 16.52/2.47    inference(resolution,[],[f1898,f41])).
% 16.52/2.47  fof(f41,plain,(
% 16.52/2.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 16.52/2.47    inference(cnf_transformation,[],[f9])).
% 16.52/2.47  fof(f9,axiom,(
% 16.52/2.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 16.52/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 16.52/2.47  fof(f71,plain,(
% 16.52/2.47    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_xboole_0(X0,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 16.52/2.47    inference(equality_resolution,[],[f62])).
% 16.52/2.47  fof(f62,plain,(
% 16.52/2.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 16.52/2.47    inference(cnf_transformation,[],[f3])).
% 16.52/2.47  fof(f16749,plain,(
% 16.52/2.47    sK0 != sK2),
% 16.52/2.47    inference(trivial_inequality_removal,[],[f16748])).
% 16.52/2.47  fof(f16748,plain,(
% 16.52/2.47    sK1 != sK1 | sK0 != sK2),
% 16.52/2.47    inference(superposition,[],[f29,f12734])).
% 16.52/2.47  fof(f12734,plain,(
% 16.52/2.47    sK1 = sK3),
% 16.52/2.47    inference(resolution,[],[f12732,f1327])).
% 16.52/2.47  fof(f1327,plain,(
% 16.52/2.47    ~r1_tarski(sK3,sK1) | sK1 = sK3),
% 16.52/2.47    inference(resolution,[],[f1324,f41])).
% 16.52/2.47  fof(f12732,plain,(
% 16.52/2.47    r1_tarski(sK3,sK1)),
% 16.52/2.47    inference(duplicate_literal_removal,[],[f12724])).
% 16.52/2.47  fof(f12724,plain,(
% 16.52/2.47    r1_tarski(sK3,sK1) | r1_tarski(sK3,sK1)),
% 16.52/2.47    inference(resolution,[],[f12341,f45])).
% 16.52/2.47  fof(f12341,plain,(
% 16.52/2.47    ( ! [X18] : (r2_hidden(sK5(sK3,X18),sK1) | r1_tarski(sK3,X18)) )),
% 16.52/2.47    inference(resolution,[],[f12312,f44])).
% 16.52/2.47  fof(f12312,plain,(
% 16.52/2.47    ( ! [X9] : (~r2_hidden(X9,sK3) | r2_hidden(X9,sK1)) )),
% 16.52/2.47    inference(subsumption_resolution,[],[f12266,f9653])).
% 16.52/2.47  fof(f12266,plain,(
% 16.52/2.47    ( ! [X9] : (r2_hidden(X9,k1_xboole_0) | r2_hidden(X9,sK1) | ~r2_hidden(X9,sK3)) )),
% 16.52/2.47    inference(superposition,[],[f68,f12244])).
% 16.52/2.47  fof(f12244,plain,(
% 16.52/2.47    k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 16.52/2.47    inference(resolution,[],[f12241,f35])).
% 16.52/2.47  fof(f12241,plain,(
% 16.52/2.47    v1_xboole_0(k4_xboole_0(sK3,sK1))),
% 16.52/2.47    inference(duplicate_literal_removal,[],[f12238])).
% 16.52/2.47  fof(f12238,plain,(
% 16.52/2.47    v1_xboole_0(k4_xboole_0(sK3,sK1)) | v1_xboole_0(k4_xboole_0(sK3,sK1))),
% 16.52/2.47    inference(resolution,[],[f12122,f80])).
% 16.52/2.47  fof(f12122,plain,(
% 16.52/2.47    ( ! [X2] : (~r2_hidden(sK4(k4_xboole_0(X2,sK1)),sK3) | v1_xboole_0(k4_xboole_0(X2,sK1))) )),
% 16.52/2.47    inference(resolution,[],[f12108,f36])).
% 16.52/2.47  fof(f12108,plain,(
% 16.52/2.47    ( ! [X8,X9] : (~r2_hidden(X9,k4_xboole_0(X8,sK1)) | ~r2_hidden(X9,sK3)) )),
% 16.52/2.47    inference(subsumption_resolution,[],[f12068,f9653])).
% 16.52/2.47  fof(f12068,plain,(
% 16.52/2.47    ( ! [X8,X9] : (r2_hidden(X9,k1_xboole_0) | ~r2_hidden(X9,k4_xboole_0(X8,sK1)) | ~r2_hidden(X9,sK3)) )),
% 16.52/2.47    inference(superposition,[],[f71,f12059])).
% 16.52/2.47  fof(f12059,plain,(
% 16.52/2.47    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X3,sK1))) )),
% 16.52/2.47    inference(subsumption_resolution,[],[f12056,f66])).
% 16.52/2.47  fof(f12056,plain,(
% 16.52/2.47    ( ! [X3] : (k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X3,sK1))) )),
% 16.52/2.47    inference(superposition,[],[f5012,f750])).
% 16.52/2.47  fof(f5012,plain,(
% 16.52/2.47    ( ! [X16] : (k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X16)) | k1_xboole_0 = k3_xboole_0(sK3,X16)) )),
% 16.52/2.47    inference(subsumption_resolution,[],[f4990,f31])).
% 16.52/2.47  fof(f4990,plain,(
% 16.52/2.47    ( ! [X16] : (k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X16)) | k1_xboole_0 = k3_xboole_0(sK3,X16) | k1_xboole_0 = sK0) )),
% 16.52/2.47    inference(superposition,[],[f46,f4399])).
% 16.52/2.47  fof(f4399,plain,(
% 16.52/2.47    ( ! [X9] : (k2_zfmisc_1(sK0,k3_xboole_0(sK1,X9)) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,X9))) )),
% 16.52/2.47    inference(forward_demodulation,[],[f4383,f224])).
% 16.52/2.47  fof(f4383,plain,(
% 16.52/2.47    ( ! [X9] : (k2_zfmisc_1(sK0,k3_xboole_0(sK3,X9)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X9))) )),
% 16.52/2.47    inference(superposition,[],[f224,f4367])).
% 16.52/2.47  fof(f4367,plain,(
% 16.52/2.47    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 16.52/2.47    inference(subsumption_resolution,[],[f4365,f1855])).
% 16.52/2.47  fof(f4365,plain,(
% 16.52/2.47    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 16.52/2.47    inference(resolution,[],[f4348,f41])).
% 16.52/2.47  fof(f4348,plain,(
% 16.52/2.47    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1))),
% 16.52/2.47    inference(superposition,[],[f4275,f30])).
% 16.52/2.47  fof(f4275,plain,(
% 16.52/2.47    ( ! [X153] : (r1_tarski(k2_zfmisc_1(sK0,X153),k2_zfmisc_1(sK2,X153))) )),
% 16.52/2.47    inference(superposition,[],[f2502,f2730])).
% 16.52/2.47  fof(f2730,plain,(
% 16.52/2.47    sK0 = k3_xboole_0(sK0,sK2)),
% 16.52/2.47    inference(resolution,[],[f2726,f38])).
% 16.52/2.47  fof(f2726,plain,(
% 16.52/2.47    r1_tarski(sK0,sK2)),
% 16.52/2.47    inference(duplicate_literal_removal,[],[f2717])).
% 16.52/2.47  fof(f2717,plain,(
% 16.52/2.47    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2)),
% 16.52/2.47    inference(resolution,[],[f2678,f44])).
% 16.52/2.47  fof(f2678,plain,(
% 16.52/2.47    ( ! [X0] : (~r2_hidden(sK5(X0,sK2),sK0) | r1_tarski(X0,sK2)) )),
% 16.52/2.47    inference(resolution,[],[f2672,f45])).
% 16.52/2.47  fof(f2672,plain,(
% 16.52/2.47    ( ! [X17] : (r2_hidden(X17,sK2) | ~r2_hidden(X17,sK0)) )),
% 16.52/2.47    inference(subsumption_resolution,[],[f2637,f92])).
% 16.52/2.47  fof(f2637,plain,(
% 16.52/2.47    ( ! [X17] : (r2_hidden(X17,k1_xboole_0) | r2_hidden(X17,sK2) | ~r2_hidden(X17,sK0)) )),
% 16.52/2.47    inference(superposition,[],[f68,f2611])).
% 16.52/2.47  fof(f2611,plain,(
% 16.52/2.47    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 16.52/2.47    inference(subsumption_resolution,[],[f2605,f32])).
% 16.52/2.47  fof(f2605,plain,(
% 16.52/2.47    k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 16.52/2.47    inference(trivial_inequality_removal,[],[f2593])).
% 16.52/2.47  fof(f2593,plain,(
% 16.52/2.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 16.52/2.47    inference(superposition,[],[f46,f2539])).
% 16.52/2.47  fof(f2539,plain,(
% 16.52/2.47    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 16.52/2.47    inference(superposition,[],[f2466,f210])).
% 16.52/2.47  fof(f2466,plain,(
% 16.52/2.47    ( ! [X11] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(X11,sK2),sK0),sK1)) )),
% 16.52/2.47    inference(superposition,[],[f228,f448])).
% 16.52/2.47  fof(f448,plain,(
% 16.52/2.47    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X12,sK2),X13),k2_zfmisc_1(sK0,sK1))) )),
% 16.52/2.47    inference(superposition,[],[f435,f30])).
% 16.52/2.47  fof(f435,plain,(
% 16.52/2.47    ( ! [X4,X2,X5,X3] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X2,X3),X4),k2_zfmisc_1(X3,X5))) )),
% 16.52/2.47    inference(forward_demodulation,[],[f417,f67])).
% 16.52/2.47  fof(f417,plain,(
% 16.52/2.47    ( ! [X4,X2,X5,X3] : (k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X2,X3),X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X4,X5))) )),
% 16.52/2.47    inference(superposition,[],[f63,f392])).
% 16.52/2.47  fof(f2502,plain,(
% 16.52/2.47    ( ! [X80,X81,X82] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X80,X82),X81),k2_zfmisc_1(X82,X81))) )),
% 16.52/2.47    inference(superposition,[],[f254,f228])).
% 16.52/2.47  fof(f29,plain,(
% 16.52/2.47    sK1 != sK3 | sK0 != sK2),
% 16.52/2.47    inference(cnf_transformation,[],[f21])).
% 16.52/2.47  fof(f2729,plain,(
% 16.52/2.47    ~r1_tarski(sK2,sK0) | sK0 = sK2),
% 16.52/2.47    inference(resolution,[],[f2726,f41])).
% 16.52/2.47  % SZS output end Proof for theBenchmark
% 16.52/2.47  % (351)------------------------------
% 16.52/2.47  % (351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.52/2.47  % (351)Termination reason: Refutation
% 16.52/2.47  
% 16.52/2.47  % (351)Memory used [KB]: 29423
% 16.52/2.47  % (351)Time elapsed: 2.002 s
% 16.52/2.47  % (351)------------------------------
% 16.52/2.47  % (351)------------------------------
% 16.52/2.49  % (344)Success in time 2.128 s
%------------------------------------------------------------------------------
