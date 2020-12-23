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
% DateTime   : Thu Dec  3 12:43:14 EST 2020

% Result     : Theorem 3.33s
% Output     : Refutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  182 (51433 expanded)
%              Number of leaves         :   21 (12457 expanded)
%              Depth                    :   38
%              Number of atoms          :  322 (156407 expanded)
%              Number of equality atoms :  133 (45768 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3945,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f1426,f2015,f79,f3011])).

fof(f3011,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X6,k1_tarski(sK0))
      | ~ r2_hidden(X5,X6)
      | ~ r2_hidden(sK1,X6) ) ),
    inference(superposition,[],[f2095,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X2,X3)) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f2095,plain,(
    ! [X0,X1] : ~ r1_tarski(k2_xboole_0(k2_xboole_0(k1_tarski(sK1),X0),X1),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f356,f2056,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f101,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f101,plain,(
    ! [X4,X2,X5,X3] :
      ( r2_hidden(sK4(X2,X4),X5)
      | r1_tarski(X2,X4)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X5) ) ),
    inference(resolution,[],[f86,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2056,plain,(
    ~ r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f35,f969])).

fof(f969,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X2),k1_tarski(X3))
      | X2 = X3 ) ),
    inference(trivial_inequality_removal,[],[f966])).

fof(f966,plain,(
    ! [X2,X3] :
      ( k1_tarski(X2) != k1_tarski(X2)
      | X2 = X3
      | ~ r1_tarski(k1_tarski(X2),k1_tarski(X3)) ) ),
    inference(superposition,[],[f74,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f42,f41,f41])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k4_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f46,f66])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f35,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(f356,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(unit_resulting_resolution,[],[f335,f335,f111])).

fof(f335,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f208,f333])).

fof(f333,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f332,f128])).

fof(f128,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f79,f127])).

fof(f127,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X3,X2) ) ),
    inference(global_subsumption,[],[f79,f125])).

fof(f125,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X2)
      | ~ r1_tarski(X3,X2)
      | k2_xboole_0(X3,X2) = X2 ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X2)
      | ~ r1_tarski(X3,X2)
      | k2_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X2)
      | ~ r1_tarski(X3,X2)
      | k2_xboole_0(X3,X2) = X2 ) ),
    inference(resolution,[],[f64,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK5(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK5(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f332,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X0)),k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f291,f128])).

fof(f291,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),k2_xboole_0(X0,X0)),k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) = X0 ),
    inference(unit_resulting_resolution,[],[f79,f73])).

fof(f208,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))),k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f178,f128])).

fof(f178,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f77,f128])).

fof(f77,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))),k2_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f58,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2015,plain,(
    r2_hidden(sK1,k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f90,f1774])).

fof(f1774,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(trivial_inequality_removal,[],[f1762])).

fof(f1762,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(backward_demodulation,[],[f521,f1710])).

fof(f1710,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f1582,f642])).

fof(f642,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(forward_demodulation,[],[f622,f597])).

fof(f597,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f561,f127])).

fof(f561,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f552,f156])).

fof(f156,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f128,f70])).

fof(f70,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f552,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
    inference(unit_resulting_resolution,[],[f365,f536,f86])).

fof(f536,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f525,f334])).

fof(f334,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(backward_demodulation,[],[f275,f333])).

fof(f275,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))))
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(forward_demodulation,[],[f253,f128])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))))
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f72,f128])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f525,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f524])).

fof(f524,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f523,f156])).

fof(f523,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f522,f128])).

fof(f522,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f497,f128])).

fof(f497,plain,
    ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)))
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f76,f156])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f365,plain,(
    ! [X11] : r1_tarski(k4_xboole_0(X11,k1_xboole_0),X11) ),
    inference(superposition,[],[f335,f70])).

fof(f622,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = k2_xboole_0(k1_xboole_0,X2) ) ),
    inference(backward_demodulation,[],[f226,f597])).

fof(f226,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_xboole_0(k1_xboole_0,X2),k1_xboole_0)
      | k1_xboole_0 = k2_xboole_0(k1_xboole_0,X2) ) ),
    inference(resolution,[],[f215,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f215,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,X5)) ),
    inference(forward_demodulation,[],[f214,f156])).

fof(f214,plain,(
    ! [X5] : r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,X5)) ),
    inference(forward_demodulation,[],[f213,f128])).

fof(f213,plain,(
    ! [X5] : r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)),k2_xboole_0(k1_xboole_0,X5)) ),
    inference(forward_demodulation,[],[f189,f128])).

fof(f189,plain,(
    ! [X5] : r1_tarski(k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))),k2_xboole_0(k1_xboole_0,X5)) ),
    inference(superposition,[],[f77,f156])).

fof(f1582,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(global_subsumption,[],[f1105,f1573])).

fof(f1573,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,k1_xboole_0)
      | r1_tarski(k4_xboole_0(X0,X0),X1) ) ),
    inference(resolution,[],[f799,f53])).

fof(f799,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(X0,X0))
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f775,f128])).

fof(f775,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f269,f751])).

fof(f751,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f708,f731])).

fof(f731,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f720,f597])).

fof(f720,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f597,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f708,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f534,f691])).

fof(f691,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f632,f98])).

fof(f98,plain,(
    ! [X0] :
      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0
      | ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ) ),
    inference(forward_demodulation,[],[f92,f39])).

fof(f92,plain,(
    ! [X0] :
      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0) = X0
      | ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ) ),
    inference(superposition,[],[f60,f70])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f632,plain,(
    ! [X18] : r1_xboole_0(k1_xboole_0,X18) ),
    inference(backward_demodulation,[],[f517,f597])).

fof(f517,plain,(
    ! [X18] : r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X18)) ),
    inference(trivial_inequality_removal,[],[f516])).

fof(f516,plain,(
    ! [X18] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X18)) ) ),
    inference(forward_demodulation,[],[f493,f328])).

fof(f328,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)),k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f293,f224])).

fof(f224,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f215,f127])).

fof(f293,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)),k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)),k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f215,f73])).

fof(f493,plain,(
    ! [X18] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X18),k1_xboole_0)),k2_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X18),k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X18),k1_xboole_0))))
      | r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X18)) ) ),
    inference(superposition,[],[f76,f224])).

fof(f534,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f525,f60])).

fof(f269,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0)))
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f72,f70])).

fof(f1105,plain,(
    ! [X11] : r1_xboole_0(X11,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1104,f1064])).

fof(f1064,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f1063,f128])).

fof(f1063,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1062,f156])).

fof(f1062,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1061,f746])).

fof(f746,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0))) ),
    inference(backward_demodulation,[],[f627,f731])).

fof(f627,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k1_xboole_0)),X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k1_xboole_0)))) ),
    inference(backward_demodulation,[],[f328,f597])).

fof(f1061,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)))),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)))) ),
    inference(forward_demodulation,[],[f1060,f731])).

fof(f1060,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0))))),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0))))) ),
    inference(forward_demodulation,[],[f1011,f731])).

fof(f1011,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0))))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)))),k1_xboole_0)) ),
    inference(superposition,[],[f69,f597])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))),X0)) ),
    inference(definition_unfolding,[],[f38,f41,f66])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1104,plain,(
    ! [X11] : r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)) ),
    inference(trivial_inequality_removal,[],[f1103])).

fof(f1103,plain,(
    ! [X11] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)) ) ),
    inference(forward_demodulation,[],[f1102,f1087])).

fof(f1087,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f1068,f597])).

fof(f1068,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0),k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) ),
    inference(backward_demodulation,[],[f746,f1064])).

fof(f1102,plain,(
    ! [X11] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(X11,X11),k4_xboole_0(X11,X11))
      | r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)) ) ),
    inference(forward_demodulation,[],[f1101,f731])).

fof(f1101,plain,(
    ! [X11] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k1_xboole_0),X11),k4_xboole_0(X11,k4_xboole_0(X11,k1_xboole_0)))
      | r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)) ) ),
    inference(forward_demodulation,[],[f1100,f751])).

fof(f1100,plain,(
    ! [X11] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X11,k1_xboole_0),k1_xboole_0),X11),k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,k1_xboole_0),k1_xboole_0)))
      | r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)) ) ),
    inference(forward_demodulation,[],[f1072,f1064])).

fof(f1072,plain,(
    ! [X11] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11)),X11),k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11))))
      | r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)) ) ),
    inference(backward_demodulation,[],[f766,f1064])).

fof(f766,plain,(
    ! [X11] :
      ( r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11))
      | k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),X11)),X11),k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),X11)))) ) ),
    inference(forward_demodulation,[],[f745,f731])).

fof(f745,plain,(
    ! [X11] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),X11)),X11),k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),X11))))
      | r1_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11)) ) ),
    inference(backward_demodulation,[],[f488,f731])).

fof(f488,plain,(
    ! [X11] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(X11,k1_xboole_0))),X11),k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(X11,k1_xboole_0)))))
      | r1_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11)) ) ),
    inference(superposition,[],[f76,f70])).

fof(f521,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(X0),X1))
      | r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f520,f128])).

fof(f520,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(X0),X1)),k4_xboole_0(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(X0),X1)))
      | r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f495,f39])).

fof(f495,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))),k2_xboole_0(k1_tarski(X0),X1)),k4_xboole_0(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))))
      | r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f76,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f90,plain,(
    ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f60])).

fof(f36,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f1426,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(global_subsumption,[],[f81,f1415])).

fof(f1415,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X0))
      | r2_hidden(X0,k1_tarski(X0)) ) ),
    inference(superposition,[],[f1406,f55])).

fof(f1406,plain,(
    ! [X7] : r1_xboole_0(k4_xboole_0(X7,X7),X7) ),
    inference(trivial_inequality_removal,[],[f1405])).

fof(f1405,plain,(
    ! [X7] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k4_xboole_0(X7,X7),X7) ) ),
    inference(forward_demodulation,[],[f1404,f1087])).

fof(f1404,plain,(
    ! [X7] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(X7,X7),k4_xboole_0(X7,X7))
      | r1_xboole_0(k4_xboole_0(X7,X7),X7) ) ),
    inference(forward_demodulation,[],[f1403,f1393])).

fof(f1393,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(backward_demodulation,[],[f333,f1392])).

fof(f1392,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X1,X1),X1) ),
    inference(forward_demodulation,[],[f1391,f751])).

fof(f1391,plain,(
    ! [X1] : k4_xboole_0(k4_xboole_0(X1,X1),X1) = k2_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1390,f731])).

fof(f1390,plain,(
    ! [X1] : k4_xboole_0(k4_xboole_0(X1,X1),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1389,f1064])).

fof(f1389,plain,(
    ! [X1] : k4_xboole_0(k4_xboole_0(X1,X1),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))) ),
    inference(forward_demodulation,[],[f1388,f1087])).

fof(f1388,plain,(
    ! [X1] : k4_xboole_0(k4_xboole_0(X1,X1),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1))) ),
    inference(forward_demodulation,[],[f1373,f333])).

fof(f1373,plain,(
    ! [X1] : k4_xboole_0(k4_xboole_0(X1,X1),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,X1)))))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))))),k4_xboole_0(X1,X1))) ),
    inference(superposition,[],[f69,f1334])).

fof(f1334,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f1291,f127])).

fof(f1291,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f797,f128])).

fof(f797,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f773,f128])).

fof(f773,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),k2_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f193,f751])).

fof(f193,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0)),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f77,f70])).

fof(f1403,plain,(
    ! [X7] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X7,X7),k4_xboole_0(X7,k4_xboole_0(X7,X7))),X7),k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X7),k4_xboole_0(X7,k4_xboole_0(X7,X7)))))
      | r1_xboole_0(k4_xboole_0(X7,X7),X7) ) ),
    inference(forward_demodulation,[],[f1378,f1392])).

fof(f1378,plain,(
    ! [X7] :
      ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X7),X7),k4_xboole_0(X7,k4_xboole_0(X7,X7))),X7),k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X7),X7),k4_xboole_0(X7,k4_xboole_0(X7,X7)))))
      | r1_xboole_0(k4_xboole_0(X7,X7),X7) ) ),
    inference(superposition,[],[f76,f1334])).

fof(f81,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:16:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (5430)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (5426)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (5446)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (5434)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (5438)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (5442)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (5424)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (5424)Refutation not found, incomplete strategy% (5424)------------------------------
% 0.22/0.53  % (5424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5424)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5424)Memory used [KB]: 1663
% 0.22/0.53  % (5424)Time elapsed: 0.112 s
% 0.22/0.53  % (5424)------------------------------
% 0.22/0.53  % (5424)------------------------------
% 0.22/0.53  % (5426)Refutation not found, incomplete strategy% (5426)------------------------------
% 0.22/0.53  % (5426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5426)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5426)Memory used [KB]: 10746
% 0.22/0.53  % (5426)Time elapsed: 0.110 s
% 0.22/0.53  % (5426)------------------------------
% 0.22/0.53  % (5426)------------------------------
% 0.22/0.53  % (5437)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.54  % (5451)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (5425)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (5441)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.54  % (5432)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.54  % (5446)Refutation not found, incomplete strategy% (5446)------------------------------
% 1.36/0.54  % (5446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (5446)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (5446)Memory used [KB]: 10746
% 1.36/0.54  % (5446)Time elapsed: 0.136 s
% 1.36/0.54  % (5446)------------------------------
% 1.36/0.54  % (5446)------------------------------
% 1.36/0.55  % (5428)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.55  % (5439)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.55  % (5432)Refutation not found, incomplete strategy% (5432)------------------------------
% 1.36/0.55  % (5432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (5448)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (5440)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.55  % (5433)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.55  % (5447)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.48/0.55  % (5429)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.48/0.55  % (5432)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (5432)Memory used [KB]: 10746
% 1.48/0.55  % (5432)Time elapsed: 0.136 s
% 1.48/0.55  % (5432)------------------------------
% 1.48/0.55  % (5432)------------------------------
% 1.48/0.55  % (5431)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.48/0.55  % (5443)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.56  % (5427)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.48/0.56  % (5452)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.48/0.56  % (5441)Refutation not found, incomplete strategy% (5441)------------------------------
% 1.48/0.56  % (5441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (5441)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (5441)Memory used [KB]: 10618
% 1.48/0.56  % (5441)Time elapsed: 0.149 s
% 1.48/0.56  % (5441)------------------------------
% 1.48/0.56  % (5441)------------------------------
% 1.48/0.56  % (5449)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.56  % (5444)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.56  % (5445)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.56  % (5445)Refutation not found, incomplete strategy% (5445)------------------------------
% 1.48/0.56  % (5445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (5445)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (5445)Memory used [KB]: 1791
% 1.48/0.56  % (5445)Time elapsed: 0.159 s
% 1.48/0.56  % (5445)------------------------------
% 1.48/0.56  % (5445)------------------------------
% 1.48/0.56  % (5444)Refutation not found, incomplete strategy% (5444)------------------------------
% 1.48/0.56  % (5444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (5444)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (5444)Memory used [KB]: 10746
% 1.48/0.56  % (5444)Time elapsed: 0.158 s
% 1.48/0.56  % (5444)------------------------------
% 1.48/0.56  % (5444)------------------------------
% 1.48/0.56  % (5435)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.56  % (5436)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.57  % (5450)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.58  % (5453)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.98/0.65  % (5467)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.98/0.66  % (5460)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.98/0.66  % (5459)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.27/0.69  % (5468)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.27/0.71  % (5471)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.27/0.71  % (5469)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.27/0.73  % (5470)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.81/0.80  % (5460)Refutation not found, incomplete strategy% (5460)------------------------------
% 2.81/0.80  % (5460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.80  % (5460)Termination reason: Refutation not found, incomplete strategy
% 2.81/0.80  
% 2.81/0.80  % (5460)Memory used [KB]: 6140
% 2.81/0.80  % (5460)Time elapsed: 0.243 s
% 2.81/0.80  % (5460)------------------------------
% 2.81/0.80  % (5460)------------------------------
% 2.81/0.81  % (5429)Time limit reached!
% 2.81/0.81  % (5429)------------------------------
% 2.81/0.81  % (5429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.81  % (5429)Termination reason: Time limit
% 2.81/0.81  % (5429)Termination phase: Saturation
% 2.81/0.81  
% 2.81/0.81  % (5429)Memory used [KB]: 7036
% 2.81/0.81  % (5429)Time elapsed: 0.400 s
% 2.81/0.81  % (5429)------------------------------
% 2.81/0.81  % (5429)------------------------------
% 3.33/0.91  % (5448)Refutation found. Thanks to Tanya!
% 3.33/0.91  % SZS status Theorem for theBenchmark
% 3.33/0.91  % SZS output start Proof for theBenchmark
% 3.33/0.91  fof(f3945,plain,(
% 3.33/0.91    $false),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f1426,f2015,f79,f3011])).
% 3.33/0.91  fof(f3011,plain,(
% 3.33/0.91    ( ! [X6,X5] : (~r1_tarski(X6,k1_tarski(sK0)) | ~r2_hidden(X5,X6) | ~r2_hidden(sK1,X6)) )),
% 3.33/0.91    inference(superposition,[],[f2095,f78])).
% 3.33/0.91  fof(f78,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 3.33/0.91    inference(definition_unfolding,[],[f61,f68])).
% 3.33/0.91  fof(f68,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.33/0.91    inference(definition_unfolding,[],[f40,f67])).
% 3.33/0.91  fof(f67,plain,(
% 3.33/0.91    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X2,X3))) )),
% 3.33/0.91    inference(definition_unfolding,[],[f65,f59])).
% 3.33/0.91  fof(f59,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.33/0.91    inference(cnf_transformation,[],[f16])).
% 3.33/0.91  fof(f16,axiom,(
% 3.33/0.91    ! [X0,X1,X2] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).
% 3.33/0.91  fof(f65,plain,(
% 3.33/0.91    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 3.33/0.91    inference(cnf_transformation,[],[f14])).
% 3.33/0.91  fof(f14,axiom,(
% 3.33/0.91    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 3.33/0.91  fof(f40,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.33/0.91    inference(cnf_transformation,[],[f15])).
% 3.33/0.91  fof(f15,axiom,(
% 3.33/0.91    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 3.33/0.91  fof(f61,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | k2_xboole_0(k2_tarski(X0,X2),X1) = X1) )),
% 3.33/0.91    inference(cnf_transformation,[],[f32])).
% 3.33/0.91  fof(f32,plain,(
% 3.33/0.91    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 3.33/0.91    inference(flattening,[],[f31])).
% 3.33/0.91  fof(f31,plain,(
% 3.33/0.91    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 3.33/0.91    inference(ennf_transformation,[],[f19])).
% 3.33/0.91  fof(f19,axiom,(
% 3.33/0.91    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 3.33/0.91  fof(f2095,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k2_xboole_0(k1_tarski(sK1),X0),X1),k1_tarski(sK0))) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f356,f2056,f111])).
% 3.33/0.91  fof(f111,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 3.33/0.91    inference(duplicate_literal_removal,[],[f109])).
% 3.33/0.91  fof(f109,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X2,X1) | r1_tarski(X0,X1)) )),
% 3.33/0.91    inference(resolution,[],[f101,f54])).
% 3.33/0.91  fof(f54,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.33/0.91    inference(cnf_transformation,[],[f28])).
% 3.33/0.91  fof(f28,plain,(
% 3.33/0.91    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.33/0.91    inference(ennf_transformation,[],[f1])).
% 3.33/0.91  fof(f1,axiom,(
% 3.33/0.91    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.33/0.91  fof(f101,plain,(
% 3.33/0.91    ( ! [X4,X2,X5,X3] : (r2_hidden(sK4(X2,X4),X5) | r1_tarski(X2,X4) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X5)) )),
% 3.33/0.91    inference(resolution,[],[f86,f52])).
% 3.33/0.91  fof(f52,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.33/0.91    inference(cnf_transformation,[],[f28])).
% 3.33/0.91  fof(f86,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 3.33/0.91    inference(resolution,[],[f52,f53])).
% 3.33/0.91  fof(f53,plain,(
% 3.33/0.91    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.33/0.91    inference(cnf_transformation,[],[f28])).
% 3.33/0.91  fof(f2056,plain,(
% 3.33/0.91    ~r1_tarski(k1_tarski(sK1),k1_tarski(sK0))),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f35,f969])).
% 3.33/0.91  fof(f969,plain,(
% 3.33/0.91    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X2),k1_tarski(X3)) | X2 = X3) )),
% 3.33/0.91    inference(trivial_inequality_removal,[],[f966])).
% 3.33/0.91  fof(f966,plain,(
% 3.33/0.91    ( ! [X2,X3] : (k1_tarski(X2) != k1_tarski(X2) | X2 = X3 | ~r1_tarski(k1_tarski(X2),k1_tarski(X3))) )),
% 3.33/0.91    inference(superposition,[],[f74,f73])).
% 3.33/0.91  fof(f73,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = X0 | ~r1_tarski(X0,X1)) )),
% 3.33/0.91    inference(definition_unfolding,[],[f45,f66])).
% 3.33/0.91  fof(f66,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) )),
% 3.33/0.91    inference(definition_unfolding,[],[f42,f41,f41])).
% 3.33/0.91  fof(f41,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 3.33/0.91    inference(cnf_transformation,[],[f2])).
% 3.33/0.91  fof(f2,axiom,(
% 3.33/0.91    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 3.33/0.91  fof(f42,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.33/0.91    inference(cnf_transformation,[],[f13])).
% 3.33/0.91  fof(f13,axiom,(
% 3.33/0.91    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 3.33/0.91  fof(f45,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.33/0.91    inference(cnf_transformation,[],[f26])).
% 3.33/0.91  fof(f26,plain,(
% 3.33/0.91    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.33/0.91    inference(ennf_transformation,[],[f8])).
% 3.33/0.91  fof(f8,axiom,(
% 3.33/0.91    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.33/0.91  fof(f74,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k1_tarski(X0) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k4_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) | X0 = X1) )),
% 3.33/0.91    inference(definition_unfolding,[],[f46,f66])).
% 3.33/0.91  fof(f46,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 3.33/0.91    inference(cnf_transformation,[],[f27])).
% 3.33/0.91  fof(f27,plain,(
% 3.33/0.91    ! [X0,X1] : (X0 = X1 | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.33/0.91    inference(ennf_transformation,[],[f18])).
% 3.33/0.91  fof(f18,axiom,(
% 3.33/0.91    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 3.33/0.91  fof(f35,plain,(
% 3.33/0.91    sK0 != sK1),
% 3.33/0.91    inference(cnf_transformation,[],[f24])).
% 3.33/0.91  fof(f24,plain,(
% 3.33/0.91    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1)),
% 3.33/0.91    inference(ennf_transformation,[],[f22])).
% 3.33/0.91  fof(f22,negated_conjecture,(
% 3.33/0.91    ~! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 3.33/0.91    inference(negated_conjecture,[],[f21])).
% 3.33/0.91  fof(f21,conjecture,(
% 3.33/0.91    ! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).
% 3.33/0.91  fof(f356,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f335,f335,f111])).
% 3.33/0.91  fof(f335,plain,(
% 3.33/0.91    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.33/0.91    inference(backward_demodulation,[],[f208,f333])).
% 3.33/0.91  fof(f333,plain,(
% 3.33/0.91    ( ! [X0] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = X0) )),
% 3.33/0.91    inference(forward_demodulation,[],[f332,f128])).
% 3.33/0.91  fof(f128,plain,(
% 3.33/0.91    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f79,f127])).
% 3.33/0.91  fof(f127,plain,(
% 3.33/0.91    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X2 | ~r1_tarski(X3,X2)) )),
% 3.33/0.91    inference(global_subsumption,[],[f79,f125])).
% 3.33/0.91  fof(f125,plain,(
% 3.33/0.91    ( ! [X2,X3] : (~r1_tarski(X2,X2) | ~r1_tarski(X3,X2) | k2_xboole_0(X3,X2) = X2) )),
% 3.33/0.91    inference(duplicate_literal_removal,[],[f124])).
% 3.33/0.91  fof(f124,plain,(
% 3.33/0.91    ( ! [X2,X3] : (~r1_tarski(X2,X2) | ~r1_tarski(X3,X2) | k2_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X2) | ~r1_tarski(X3,X2) | k2_xboole_0(X3,X2) = X2) )),
% 3.33/0.91    inference(resolution,[],[f64,f63])).
% 3.33/0.91  fof(f63,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (r1_tarski(X2,sK5(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1) | k2_xboole_0(X0,X2) = X1) )),
% 3.33/0.91    inference(cnf_transformation,[],[f34])).
% 3.33/0.91  fof(f34,plain,(
% 3.33/0.91    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.33/0.91    inference(flattening,[],[f33])).
% 3.33/0.91  fof(f33,plain,(
% 3.33/0.91    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.33/0.91    inference(ennf_transformation,[],[f7])).
% 3.33/0.91  fof(f7,axiom,(
% 3.33/0.91    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 3.33/0.91  fof(f64,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK5(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1) | k2_xboole_0(X0,X2) = X1) )),
% 3.33/0.91    inference(cnf_transformation,[],[f34])).
% 3.33/0.91  fof(f332,plain,(
% 3.33/0.91    ( ! [X0] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X0)),k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = X0) )),
% 3.33/0.91    inference(forward_demodulation,[],[f291,f128])).
% 3.33/0.91  fof(f291,plain,(
% 3.33/0.91    ( ! [X0] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),k2_xboole_0(X0,X0)),k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) = X0) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f79,f73])).
% 3.33/0.91  fof(f208,plain,(
% 3.33/0.91    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))),k2_xboole_0(X0,X1))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f178,f128])).
% 3.33/0.91  fof(f178,plain,(
% 3.33/0.91    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))),k2_xboole_0(X0,X1))) )),
% 3.33/0.91    inference(superposition,[],[f77,f128])).
% 3.33/0.91  fof(f77,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))),k2_xboole_0(X0,X2))) )),
% 3.33/0.91    inference(definition_unfolding,[],[f58,f66])).
% 3.33/0.91  fof(f58,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 3.33/0.91    inference(cnf_transformation,[],[f9])).
% 3.33/0.91  fof(f9,axiom,(
% 3.33/0.91    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 3.33/0.91  fof(f79,plain,(
% 3.33/0.91    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.33/0.91    inference(equality_resolution,[],[f48])).
% 3.33/0.91  fof(f48,plain,(
% 3.33/0.91    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.33/0.91    inference(cnf_transformation,[],[f5])).
% 3.33/0.91  fof(f5,axiom,(
% 3.33/0.91    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.33/0.91  fof(f2015,plain,(
% 3.33/0.91    r2_hidden(sK1,k1_tarski(sK0))),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f90,f1774])).
% 3.33/0.91  fof(f1774,plain,(
% 3.33/0.91    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.33/0.91    inference(trivial_inequality_removal,[],[f1762])).
% 3.33/0.91  fof(f1762,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.33/0.91    inference(backward_demodulation,[],[f521,f1710])).
% 3.33/0.91  fof(f1710,plain,(
% 3.33/0.91    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f1582,f642])).
% 3.33/0.91  fof(f642,plain,(
% 3.33/0.91    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2) )),
% 3.33/0.91    inference(forward_demodulation,[],[f622,f597])).
% 3.33/0.91  fof(f597,plain,(
% 3.33/0.91    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f561,f127])).
% 3.33/0.91  fof(f561,plain,(
% 3.33/0.91    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f552,f156])).
% 3.33/0.91  fof(f156,plain,(
% 3.33/0.91    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.33/0.91    inference(superposition,[],[f128,f70])).
% 3.33/0.91  fof(f70,plain,(
% 3.33/0.91    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 3.33/0.91    inference(definition_unfolding,[],[f37,f41])).
% 3.33/0.91  fof(f37,plain,(
% 3.33/0.91    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.33/0.91    inference(cnf_transformation,[],[f11])).
% 3.33/0.91  fof(f11,axiom,(
% 3.33/0.91    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 3.33/0.91  fof(f552,plain,(
% 3.33/0.91    ( ! [X0] : (r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0)) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f365,f536,f86])).
% 3.33/0.91  fof(f536,plain,(
% 3.33/0.91    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f525,f334])).
% 3.33/0.91  fof(f334,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | ~r2_hidden(X1,X0)) )),
% 3.33/0.91    inference(backward_demodulation,[],[f275,f333])).
% 3.33/0.91  fof(f275,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r2_hidden(X1,k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X0),k4_xboole_0(X0,k4_xboole_0(X0,X0)))) | ~r1_xboole_0(X0,X0)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f253,f128])).
% 3.33/0.91  fof(f253,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r2_hidden(X1,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))))) | ~r1_xboole_0(X0,X0)) )),
% 3.33/0.91    inference(superposition,[],[f72,f128])).
% 3.33/0.91  fof(f72,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) | ~r1_xboole_0(X0,X1)) )),
% 3.33/0.91    inference(definition_unfolding,[],[f43,f66])).
% 3.33/0.91  fof(f43,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.33/0.91    inference(cnf_transformation,[],[f25])).
% 3.33/0.91  fof(f25,plain,(
% 3.33/0.91    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.33/0.91    inference(ennf_transformation,[],[f23])).
% 3.33/0.91  fof(f23,plain,(
% 3.33/0.91    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.33/0.91    inference(rectify,[],[f4])).
% 3.33/0.91  fof(f4,axiom,(
% 3.33/0.91    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 3.33/0.91  fof(f525,plain,(
% 3.33/0.91    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.33/0.91    inference(trivial_inequality_removal,[],[f524])).
% 3.33/0.91  fof(f524,plain,(
% 3.33/0.91    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.33/0.91    inference(forward_demodulation,[],[f523,f156])).
% 3.33/0.91  fof(f523,plain,(
% 3.33/0.91    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.33/0.91    inference(forward_demodulation,[],[f522,f128])).
% 3.33/0.91  fof(f522,plain,(
% 3.33/0.91    k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) | r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.33/0.91    inference(forward_demodulation,[],[f497,f128])).
% 3.33/0.91  fof(f497,plain,(
% 3.33/0.91    k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) | r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.33/0.91    inference(superposition,[],[f76,f156])).
% 3.33/0.91  fof(f76,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) | r1_xboole_0(X0,X1)) )),
% 3.33/0.91    inference(definition_unfolding,[],[f50,f66])).
% 3.33/0.91  fof(f50,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 3.33/0.91    inference(cnf_transformation,[],[f3])).
% 3.33/0.91  fof(f3,axiom,(
% 3.33/0.91    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 3.33/0.91  fof(f365,plain,(
% 3.33/0.91    ( ! [X11] : (r1_tarski(k4_xboole_0(X11,k1_xboole_0),X11)) )),
% 3.33/0.91    inference(superposition,[],[f335,f70])).
% 3.33/0.91  fof(f622,plain,(
% 3.33/0.91    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = k2_xboole_0(k1_xboole_0,X2)) )),
% 3.33/0.91    inference(backward_demodulation,[],[f226,f597])).
% 3.33/0.91  fof(f226,plain,(
% 3.33/0.91    ( ! [X2] : (~r1_tarski(k2_xboole_0(k1_xboole_0,X2),k1_xboole_0) | k1_xboole_0 = k2_xboole_0(k1_xboole_0,X2)) )),
% 3.33/0.91    inference(resolution,[],[f215,f49])).
% 3.33/0.91  fof(f49,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 3.33/0.91    inference(cnf_transformation,[],[f5])).
% 3.33/0.91  fof(f215,plain,(
% 3.33/0.91    ( ! [X5] : (r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,X5))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f214,f156])).
% 3.33/0.91  fof(f214,plain,(
% 3.33/0.91    ( ! [X5] : (r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,X5))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f213,f128])).
% 3.33/0.91  fof(f213,plain,(
% 3.33/0.91    ( ! [X5] : (r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)),k2_xboole_0(k1_xboole_0,X5))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f189,f128])).
% 3.33/0.91  fof(f189,plain,(
% 3.33/0.91    ( ! [X5] : (r1_tarski(k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))),k2_xboole_0(k1_xboole_0,X5))) )),
% 3.33/0.91    inference(superposition,[],[f77,f156])).
% 3.33/0.91  fof(f1582,plain,(
% 3.33/0.91    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 3.33/0.91    inference(global_subsumption,[],[f1105,f1573])).
% 3.33/0.91  fof(f1573,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r1_xboole_0(X0,k1_xboole_0) | r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 3.33/0.91    inference(resolution,[],[f799,f53])).
% 3.33/0.91  fof(f799,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0)) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f775,f128])).
% 3.33/0.91  fof(f775,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r2_hidden(X1,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 3.33/0.91    inference(backward_demodulation,[],[f269,f751])).
% 3.33/0.91  fof(f751,plain,(
% 3.33/0.91    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.33/0.91    inference(backward_demodulation,[],[f708,f731])).
% 3.33/0.91  fof(f731,plain,(
% 3.33/0.91    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 3.33/0.91    inference(forward_demodulation,[],[f720,f597])).
% 3.33/0.91  fof(f720,plain,(
% 3.33/0.91    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,k1_xboole_0)) )),
% 3.33/0.91    inference(superposition,[],[f597,f39])).
% 3.33/0.91  fof(f39,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.33/0.91    inference(cnf_transformation,[],[f10])).
% 3.33/0.91  fof(f10,axiom,(
% 3.33/0.91    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.33/0.91  fof(f708,plain,(
% 3.33/0.91    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 3.33/0.91    inference(backward_demodulation,[],[f534,f691])).
% 3.33/0.91  fof(f691,plain,(
% 3.33/0.91    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f632,f98])).
% 3.33/0.91  fof(f98,plain,(
% 3.33/0.91    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 | ~r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f92,f39])).
% 3.33/0.91  fof(f92,plain,(
% 3.33/0.91    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0) = X0 | ~r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 3.33/0.91    inference(superposition,[],[f60,f70])).
% 3.33/0.91  fof(f60,plain,(
% 3.33/0.91    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 3.33/0.91    inference(cnf_transformation,[],[f30])).
% 3.33/0.91  fof(f30,plain,(
% 3.33/0.91    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 3.33/0.91    inference(ennf_transformation,[],[f12])).
% 3.33/0.91  fof(f12,axiom,(
% 3.33/0.91    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).
% 3.33/0.91  fof(f632,plain,(
% 3.33/0.91    ( ! [X18] : (r1_xboole_0(k1_xboole_0,X18)) )),
% 3.33/0.91    inference(backward_demodulation,[],[f517,f597])).
% 3.33/0.91  fof(f517,plain,(
% 3.33/0.91    ( ! [X18] : (r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X18))) )),
% 3.33/0.91    inference(trivial_inequality_removal,[],[f516])).
% 3.33/0.91  fof(f516,plain,(
% 3.33/0.91    ( ! [X18] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X18))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f493,f328])).
% 3.33/0.91  fof(f328,plain,(
% 3.33/0.91    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)),k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0))))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f293,f224])).
% 3.33/0.91  fof(f224,plain,(
% 3.33/0.91    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f215,f127])).
% 3.33/0.91  fof(f293,plain,(
% 3.33/0.91    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)),k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)),k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0))))) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f215,f73])).
% 3.33/0.91  fof(f493,plain,(
% 3.33/0.91    ( ! [X18] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X18),k1_xboole_0)),k2_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X18),k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k2_xboole_0(k1_xboole_0,X18),k1_xboole_0)))) | r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X18))) )),
% 3.33/0.91    inference(superposition,[],[f76,f224])).
% 3.33/0.91  fof(f534,plain,(
% 3.33/0.91    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f525,f60])).
% 3.33/0.91  fof(f269,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r2_hidden(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0))) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 3.33/0.91    inference(superposition,[],[f72,f70])).
% 3.33/0.91  fof(f1105,plain,(
% 3.33/0.91    ( ! [X11] : (r1_xboole_0(X11,k1_xboole_0)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1104,f1064])).
% 3.33/0.91  fof(f1064,plain,(
% 3.33/0.91    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1063,f128])).
% 3.33/0.91  fof(f1063,plain,(
% 3.33/0.91    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1062,f156])).
% 3.33/0.91  fof(f1062,plain,(
% 3.33/0.91    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1061,f746])).
% 3.33/0.91  fof(f746,plain,(
% 3.33/0.91    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)))) )),
% 3.33/0.91    inference(backward_demodulation,[],[f627,f731])).
% 3.33/0.91  fof(f627,plain,(
% 3.33/0.91    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k1_xboole_0)),X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k1_xboole_0))))) )),
% 3.33/0.91    inference(backward_demodulation,[],[f328,f597])).
% 3.33/0.91  fof(f1061,plain,(
% 3.33/0.91    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)))),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1))))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1060,f731])).
% 3.33/0.91  fof(f1060,plain,(
% 3.33/0.91    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0))))),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)))))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1011,f731])).
% 3.33/0.91  fof(f1011,plain,(
% 3.33/0.91    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0))))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)))),k1_xboole_0))) )),
% 3.33/0.91    inference(superposition,[],[f69,f597])).
% 3.33/0.91  fof(f69,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))),X0))) )),
% 3.33/0.91    inference(definition_unfolding,[],[f38,f41,f66])).
% 3.33/0.91  fof(f38,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.33/0.91    inference(cnf_transformation,[],[f6])).
% 3.33/0.91  fof(f6,axiom,(
% 3.33/0.91    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.33/0.91  fof(f1104,plain,(
% 3.33/0.91    ( ! [X11] : (r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11))) )),
% 3.33/0.91    inference(trivial_inequality_removal,[],[f1103])).
% 3.33/0.91  fof(f1103,plain,(
% 3.33/0.91    ( ! [X11] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1102,f1087])).
% 3.33/0.91  fof(f1087,plain,(
% 3.33/0.91    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1068,f597])).
% 3.33/0.91  fof(f1068,plain,(
% 3.33/0.91    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0),k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0)))) )),
% 3.33/0.91    inference(backward_demodulation,[],[f746,f1064])).
% 3.33/0.91  fof(f1102,plain,(
% 3.33/0.91    ( ! [X11] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(X11,X11),k4_xboole_0(X11,X11)) | r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1101,f731])).
% 3.33/0.91  fof(f1101,plain,(
% 3.33/0.91    ( ! [X11] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k1_xboole_0),X11),k4_xboole_0(X11,k4_xboole_0(X11,k1_xboole_0))) | r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1100,f751])).
% 3.33/0.91  fof(f1100,plain,(
% 3.33/0.91    ( ! [X11] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X11,k1_xboole_0),k1_xboole_0),X11),k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,k1_xboole_0),k1_xboole_0))) | r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1072,f1064])).
% 3.33/0.91  fof(f1072,plain,(
% 3.33/0.91    ( ! [X11] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11)),X11),k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11)))) | r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11))) )),
% 3.33/0.91    inference(backward_demodulation,[],[f766,f1064])).
% 3.33/0.91  fof(f766,plain,(
% 3.33/0.91    ( ! [X11] : (r1_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)) | k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),X11)),X11),k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),X11))))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f745,f731])).
% 3.33/0.91  fof(f745,plain,(
% 3.33/0.91    ( ! [X11] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),X11)),X11),k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),X11)))) | r1_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11))) )),
% 3.33/0.91    inference(backward_demodulation,[],[f488,f731])).
% 3.33/0.91  fof(f488,plain,(
% 3.33/0.91    ( ! [X11] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(X11,k1_xboole_0))),X11),k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(X11,k1_xboole_0))))) | r1_xboole_0(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(k1_xboole_0,X11))) )),
% 3.33/0.91    inference(superposition,[],[f76,f70])).
% 3.33/0.91  fof(f521,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(X0),X1)) | r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f520,f128])).
% 3.33/0.91  fof(f520,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(X0),X1)),k4_xboole_0(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(X0),X1))) | r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f495,f39])).
% 3.33/0.91  fof(f495,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))),k2_xboole_0(k1_tarski(X0),X1)),k4_xboole_0(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))))) | r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.33/0.91    inference(superposition,[],[f76,f55])).
% 3.33/0.91  fof(f55,plain,(
% 3.33/0.91    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.33/0.91    inference(cnf_transformation,[],[f20])).
% 3.33/0.91  fof(f20,axiom,(
% 3.33/0.91    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 3.33/0.91  fof(f90,plain,(
% 3.33/0.91    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f36,f60])).
% 3.33/0.91  fof(f36,plain,(
% 3.33/0.91    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))),
% 3.33/0.91    inference(cnf_transformation,[],[f24])).
% 3.33/0.91  fof(f1426,plain,(
% 3.33/0.91    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 3.33/0.91    inference(global_subsumption,[],[f81,f1415])).
% 3.33/0.91  fof(f1415,plain,(
% 3.33/0.91    ( ! [X0] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X0)) | r2_hidden(X0,k1_tarski(X0))) )),
% 3.33/0.91    inference(superposition,[],[f1406,f55])).
% 3.33/0.91  fof(f1406,plain,(
% 3.33/0.91    ( ! [X7] : (r1_xboole_0(k4_xboole_0(X7,X7),X7)) )),
% 3.33/0.91    inference(trivial_inequality_removal,[],[f1405])).
% 3.33/0.91  fof(f1405,plain,(
% 3.33/0.91    ( ! [X7] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k4_xboole_0(X7,X7),X7)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1404,f1087])).
% 3.33/0.91  fof(f1404,plain,(
% 3.33/0.91    ( ! [X7] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(X7,X7),k4_xboole_0(X7,X7)) | r1_xboole_0(k4_xboole_0(X7,X7),X7)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1403,f1393])).
% 3.33/0.91  fof(f1393,plain,(
% 3.33/0.91    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = X0) )),
% 3.33/0.91    inference(backward_demodulation,[],[f333,f1392])).
% 3.33/0.91  fof(f1392,plain,(
% 3.33/0.91    ( ! [X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X1,X1),X1)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1391,f751])).
% 3.33/0.91  fof(f1391,plain,(
% 3.33/0.91    ( ! [X1] : (k4_xboole_0(k4_xboole_0(X1,X1),X1) = k2_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1390,f731])).
% 3.33/0.91  fof(f1390,plain,(
% 3.33/0.91    ( ! [X1] : (k4_xboole_0(k4_xboole_0(X1,X1),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0),k1_xboole_0)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1389,f1064])).
% 3.33/0.91  fof(f1389,plain,(
% 3.33/0.91    ( ! [X1] : (k4_xboole_0(k4_xboole_0(X1,X1),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1388,f1087])).
% 3.33/0.91  fof(f1388,plain,(
% 3.33/0.91    ( ! [X1] : (k4_xboole_0(k4_xboole_0(X1,X1),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1373,f333])).
% 3.33/0.91  fof(f1373,plain,(
% 3.33/0.91    ( ! [X1] : (k4_xboole_0(k4_xboole_0(X1,X1),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,X1)))))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))))),k4_xboole_0(X1,X1)))) )),
% 3.33/0.91    inference(superposition,[],[f69,f1334])).
% 3.33/0.91  fof(f1334,plain,(
% 3.33/0.91    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0) )),
% 3.33/0.91    inference(unit_resulting_resolution,[],[f1291,f127])).
% 3.33/0.91  fof(f1291,plain,(
% 3.33/0.91    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,X0),X0)) )),
% 3.33/0.91    inference(superposition,[],[f797,f128])).
% 3.33/0.91  fof(f797,plain,(
% 3.33/0.91    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1))) )),
% 3.33/0.91    inference(forward_demodulation,[],[f773,f128])).
% 3.33/0.91  fof(f773,plain,(
% 3.33/0.91    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),k2_xboole_0(X0,X1))) )),
% 3.33/0.91    inference(backward_demodulation,[],[f193,f751])).
% 3.33/0.91  fof(f193,plain,(
% 3.33/0.91    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0)),k2_xboole_0(X0,X1))) )),
% 3.33/0.91    inference(superposition,[],[f77,f70])).
% 3.33/0.91  fof(f1403,plain,(
% 3.33/0.91    ( ! [X7] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X7,X7),k4_xboole_0(X7,k4_xboole_0(X7,X7))),X7),k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X7),k4_xboole_0(X7,k4_xboole_0(X7,X7))))) | r1_xboole_0(k4_xboole_0(X7,X7),X7)) )),
% 3.33/0.91    inference(forward_demodulation,[],[f1378,f1392])).
% 3.33/0.91  fof(f1378,plain,(
% 3.33/0.91    ( ! [X7] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X7),X7),k4_xboole_0(X7,k4_xboole_0(X7,X7))),X7),k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X7),X7),k4_xboole_0(X7,k4_xboole_0(X7,X7))))) | r1_xboole_0(k4_xboole_0(X7,X7),X7)) )),
% 3.33/0.91    inference(superposition,[],[f76,f1334])).
% 3.33/0.91  fof(f81,plain,(
% 3.33/0.91    ( ! [X1] : (~r1_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 3.33/0.91    inference(equality_resolution,[],[f57])).
% 3.33/0.91  fof(f57,plain,(
% 3.33/0.91    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 != X1) )),
% 3.33/0.91    inference(cnf_transformation,[],[f29])).
% 3.33/0.91  fof(f29,plain,(
% 3.33/0.91    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.33/0.91    inference(ennf_transformation,[],[f17])).
% 3.33/0.91  fof(f17,axiom,(
% 3.33/0.91    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.33/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 3.33/0.91  % SZS output end Proof for theBenchmark
% 3.33/0.91  % (5448)------------------------------
% 3.33/0.91  % (5448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.91  % (5448)Termination reason: Refutation
% 3.33/0.91  
% 3.33/0.91  % (5448)Memory used [KB]: 10234
% 3.33/0.91  % (5448)Time elapsed: 0.468 s
% 3.33/0.91  % (5448)------------------------------
% 3.33/0.91  % (5448)------------------------------
% 3.33/0.91  % (5423)Success in time 0.54 s
%------------------------------------------------------------------------------
