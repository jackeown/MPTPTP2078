%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 395 expanded)
%              Number of leaves         :   13 ( 105 expanded)
%              Depth                    :   20
%              Number of atoms          :  175 ( 958 expanded)
%              Number of equality atoms :   41 ( 170 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f588,plain,(
    $false ),
    inference(subsumption_resolution,[],[f587,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f587,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f554,f509])).

fof(f509,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f147,f508])).

fof(f508,plain,(
    ! [X1] : k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f504,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f504,plain,(
    ! [X1] : k3_subset_1(X1,k1_xboole_0) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f502,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f502,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f501,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f501,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f500,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f88,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | r1_tarski(k3_subset_1(X0,X1),X0) ) ),
    inference(subsumption_resolution,[],[f86,f30])).

fof(f30,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X0)
      | ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f84,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(k3_subset_1(X1,X0),X1) ) ),
    inference(resolution,[],[f66,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_subset_1(X1,X0),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f65,f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(k3_subset_1(X1,X0),k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f500,plain,(
    ! [X1] :
      ( ~ r1_tarski(k3_subset_1(X1,k1_xboole_0),X1)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f495,f58])).

fof(f495,plain,(
    ! [X1] :
      ( ~ r2_hidden(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1))
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f494,f30])).

fof(f494,plain,(
    ! [X1] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | ~ r2_hidden(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f160,f37])).

fof(f160,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k3_subset_1(X3,k1_xboole_0),k1_zfmisc_1(X3))
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f39,f147])).

fof(f147,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f144,f31])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f103,f58])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f101,f30])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f41,f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f554,plain,(
    sK1 = k3_subset_1(sK2,sK2) ),
    inference(backward_demodulation,[],[f150,f553])).

fof(f553,plain,(
    sK2 = k3_subset_1(sK2,sK1) ),
    inference(backward_demodulation,[],[f214,f547])).

fof(f547,plain,(
    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f522,f200])).

fof(f200,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | k5_xboole_0(X0,k3_xboole_0(X0,sK1)) = X0 ) ),
    inference(resolution,[],[f196,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f42,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f196,plain,(
    ! [X2] :
      ( r1_xboole_0(X2,sK1)
      | ~ r1_tarski(X2,sK2) ) ),
    inference(superposition,[],[f54,f192])).

fof(f192,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f191,f53])).

fof(f191,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f178,f28])).

fof(f28,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f178,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_subset_1(sK0,sK2))
      | r1_xboole_0(X1,sK2) ) ),
    inference(superposition,[],[f55,f172])).

fof(f172,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f52,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f49,f34])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f34])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f522,plain,(
    ! [X3] : r1_tarski(X3,X3) ),
    inference(forward_demodulation,[],[f506,f508])).

fof(f506,plain,(
    ! [X3] : r1_tarski(k3_subset_1(X3,k1_xboole_0),X3) ),
    inference(resolution,[],[f502,f84])).

fof(f214,plain,(
    k3_subset_1(sK2,sK1) = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f212,f52])).

fof(f212,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(subsumption_resolution,[],[f211,f27])).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f211,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f210,f91])).

% (19116)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f210,plain,
    ( ~ r1_tarski(k3_subset_1(sK2,sK1),sK2)
    | m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f168,f58])).

fof(f168,plain,
    ( ~ r2_hidden(k3_subset_1(sK2,sK1),k1_zfmisc_1(sK2))
    | m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(subsumption_resolution,[],[f167,f30])).

fof(f167,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ r2_hidden(k3_subset_1(sK2,sK1),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f156,f37])).

fof(f156,plain,
    ( ~ m1_subset_1(k3_subset_1(sK2,sK1),k1_zfmisc_1(sK2))
    | m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(superposition,[],[f39,f150])).

fof(f150,plain,(
    sK1 = k3_subset_1(sK2,k3_subset_1(sK2,sK1)) ),
    inference(resolution,[],[f144,f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (19123)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (19131)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (19123)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f588,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f587,f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    k1_xboole_0 != sK1),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.56    inference(negated_conjecture,[],[f14])).
% 0.21/0.56  fof(f14,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 0.21/0.56  fof(f587,plain,(
% 0.21/0.56    k1_xboole_0 = sK1),
% 0.21/0.56    inference(forward_demodulation,[],[f554,f509])).
% 0.21/0.56  fof(f509,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f147,f508])).
% 0.21/0.56  fof(f508,plain,(
% 0.21/0.56    ( ! [X1] : (k3_subset_1(X1,k1_xboole_0) = X1) )),
% 0.21/0.56    inference(forward_demodulation,[],[f504,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f32,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.56  fof(f504,plain,(
% 0.21/0.56    ( ! [X1] : (k3_subset_1(X1,k1_xboole_0) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.21/0.56    inference(resolution,[],[f502,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f40,f34])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.56  fof(f502,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f501,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.56  fof(f501,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(resolution,[],[f500,f91])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X0) | ~r1_tarski(X1,X0)) )),
% 0.21/0.56    inference(resolution,[],[f88,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | r1_tarski(k3_subset_1(X0,X1),X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f86,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X0) | ~r2_hidden(X1,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(resolution,[],[f84,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k3_subset_1(X1,X0),X1)) )),
% 0.21/0.56    inference(resolution,[],[f66,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f65,f30])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1))) )),
% 0.21/0.56    inference(resolution,[],[f39,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.56  fof(f500,plain,(
% 0.21/0.56    ( ! [X1] : (~r1_tarski(k3_subset_1(X1,k1_xboole_0),X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) )),
% 0.21/0.56    inference(resolution,[],[f495,f58])).
% 0.21/0.56  fof(f495,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1)) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f494,f30])).
% 0.21/0.56  fof(f494,plain,(
% 0.21/0.56    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | ~r2_hidden(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1))) )),
% 0.21/0.56    inference(resolution,[],[f160,f37])).
% 0.21/0.56  fof(f160,plain,(
% 0.21/0.56    ( ! [X3] : (~m1_subset_1(k3_subset_1(X3,k1_xboole_0),k1_zfmisc_1(X3)) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))) )),
% 0.21/0.56    inference(superposition,[],[f39,f147])).
% 0.21/0.56  fof(f147,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.56    inference(resolution,[],[f144,f31])).
% 0.21/0.56  fof(f144,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.56    inference(resolution,[],[f103,f58])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f101,f30])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~r2_hidden(X1,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(resolution,[],[f41,f37])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.56  fof(f554,plain,(
% 0.21/0.56    sK1 = k3_subset_1(sK2,sK2)),
% 0.21/0.56    inference(backward_demodulation,[],[f150,f553])).
% 0.21/0.56  fof(f553,plain,(
% 0.21/0.56    sK2 = k3_subset_1(sK2,sK1)),
% 0.21/0.56    inference(backward_demodulation,[],[f214,f547])).
% 0.21/0.56  fof(f547,plain,(
% 0.21/0.56    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))),
% 0.21/0.56    inference(resolution,[],[f522,f200])).
% 0.21/0.56  fof(f200,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(X0,sK2) | k5_xboole_0(X0,k3_xboole_0(X0,sK1)) = X0) )),
% 0.21/0.56    inference(resolution,[],[f196,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f42,f34])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 0.21/0.56    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.56  fof(f196,plain,(
% 0.21/0.56    ( ! [X2] : (r1_xboole_0(X2,sK1) | ~r1_tarski(X2,sK2)) )),
% 0.21/0.56    inference(superposition,[],[f54,f192])).
% 0.21/0.56  fof(f192,plain,(
% 0.21/0.56    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 0.21/0.56    inference(resolution,[],[f191,f53])).
% 0.21/0.56  fof(f191,plain,(
% 0.21/0.56    r1_xboole_0(sK1,sK2)),
% 0.21/0.56    inference(resolution,[],[f178,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    ( ! [X1] : (~r1_tarski(X1,k3_subset_1(sK0,sK2)) | r1_xboole_0(X1,sK2)) )),
% 0.21/0.56    inference(superposition,[],[f55,f172])).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 0.21/0.56    inference(resolution,[],[f52,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_xboole_0(X0,X2)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f49,f34])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f47,f34])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.56  fof(f522,plain,(
% 0.21/0.56    ( ! [X3] : (r1_tarski(X3,X3)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f506,f508])).
% 0.21/0.56  fof(f506,plain,(
% 0.21/0.56    ( ! [X3] : (r1_tarski(k3_subset_1(X3,k1_xboole_0),X3)) )),
% 0.21/0.56    inference(resolution,[],[f502,f84])).
% 0.21/0.56  fof(f214,plain,(
% 0.21/0.56    k3_subset_1(sK2,sK1) = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))),
% 0.21/0.56    inference(resolution,[],[f212,f52])).
% 0.21/0.56  fof(f212,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 0.21/0.56    inference(subsumption_resolution,[],[f211,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    r1_tarski(sK1,sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f211,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK2)) | ~r1_tarski(sK1,sK2)),
% 0.21/0.56    inference(resolution,[],[f210,f91])).
% 0.21/0.56  % (19116)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  fof(f210,plain,(
% 0.21/0.56    ~r1_tarski(k3_subset_1(sK2,sK1),sK2) | m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 0.21/0.56    inference(resolution,[],[f168,f58])).
% 0.21/0.56  fof(f168,plain,(
% 0.21/0.56    ~r2_hidden(k3_subset_1(sK2,sK1),k1_zfmisc_1(sK2)) | m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 0.21/0.56    inference(subsumption_resolution,[],[f167,f30])).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK2)) | ~r2_hidden(k3_subset_1(sK2,sK1),k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2))),
% 0.21/0.56    inference(resolution,[],[f156,f37])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    ~m1_subset_1(k3_subset_1(sK2,sK1),k1_zfmisc_1(sK2)) | m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 0.21/0.56    inference(superposition,[],[f39,f150])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    sK1 = k3_subset_1(sK2,k3_subset_1(sK2,sK1))),
% 0.21/0.56    inference(resolution,[],[f144,f27])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (19123)------------------------------
% 0.21/0.56  % (19123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19123)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (19123)Memory used [KB]: 6652
% 0.21/0.56  % (19123)Time elapsed: 0.095 s
% 0.21/0.56  % (19123)------------------------------
% 0.21/0.56  % (19123)------------------------------
% 0.21/0.56  % (19116)Refutation not found, incomplete strategy% (19116)------------------------------
% 0.21/0.56  % (19116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19116)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19116)Memory used [KB]: 1663
% 0.21/0.56  % (19116)Time elapsed: 0.152 s
% 0.21/0.56  % (19116)------------------------------
% 0.21/0.56  % (19116)------------------------------
% 0.21/0.56  % (19110)Success in time 0.199 s
%------------------------------------------------------------------------------
