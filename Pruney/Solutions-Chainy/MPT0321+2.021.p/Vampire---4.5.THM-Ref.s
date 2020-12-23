%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:32 EST 2020

% Result     : Theorem 14.13s
% Output     : Refutation 14.13s
% Verified   : 
% Statistics : Number of formulae       :  317 (27260 expanded)
%              Number of leaves         :   19 (7636 expanded)
%              Depth                    :   81
%              Number of atoms          :  552 (88435 expanded)
%              Number of equality atoms :  381 (77374 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31338,plain,(
    $false ),
    inference(subsumption_resolution,[],[f31337,f29876])).

fof(f29876,plain,(
    sK1 != sK3 ),
    inference(trivial_inequality_removal,[],[f28663])).

fof(f28663,plain,
    ( sK0 != sK0
    | sK1 != sK3 ),
    inference(backward_demodulation,[],[f56,f28661])).

fof(f28661,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f28660,f27721])).

fof(f27721,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[],[f26860,f53])).

fof(f53,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f26860,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(backward_demodulation,[],[f26705,f26802])).

fof(f26802,plain,(
    sK3 = k3_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f26801,f61])).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f26801,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f26755,f82])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f26755,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f81,f26496])).

fof(f26496,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f26489,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f37])).

fof(f26489,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f26488])).

fof(f26488,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f57,f25854])).

fof(f25854,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) ),
    inference(forward_demodulation,[],[f25598,f90])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f25598,plain,(
    k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) ),
    inference(backward_demodulation,[],[f101,f25597])).

fof(f25597,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f25585,f55])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f25585,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f25584])).

fof(f25584,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f57,f25468])).

fof(f25468,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(backward_demodulation,[],[f195,f25455])).

fof(f25455,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f25447,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f25447,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))) ),
    inference(forward_demodulation,[],[f25446,f2524])).

fof(f2524,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2)) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(sK3,X2))) ),
    inference(forward_demodulation,[],[f2523,f82])).

fof(f2523,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2)) = k2_zfmisc_1(sK2,k3_xboole_0(k4_xboole_0(sK3,X2),sK3)) ),
    inference(forward_demodulation,[],[f2501,f61])).

fof(f2501,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k3_xboole_0(k4_xboole_0(sK3,X2),sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2)),k1_xboole_0) ),
    inference(superposition,[],[f1301,f2408])).

fof(f2408,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(k4_xboole_0(sK3,X1),sK3)) ),
    inference(superposition,[],[f265,f96])).

fof(f96,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k4_xboole_0(X2,sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,X2),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f69,f53])).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f265,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f200,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f200,plain,(
    ! [X4] : r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X4)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f85,f97])).

fof(f97,plain,(
    ! [X3] : k2_zfmisc_1(sK2,k4_xboole_0(sK3,X3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X3)) ),
    inference(superposition,[],[f69,f53])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1301,plain,(
    ! [X2] : k4_xboole_0(k2_zfmisc_1(sK2,X2),k2_zfmisc_1(sK2,k4_xboole_0(X2,sK3))) = k2_zfmisc_1(sK2,k3_xboole_0(X2,sK3)) ),
    inference(backward_demodulation,[],[f165,f1297])).

fof(f1297,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3)) ),
    inference(forward_demodulation,[],[f1264,f81])).

fof(f1264,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,sK3))) ),
    inference(superposition,[],[f165,f69])).

fof(f165,plain,(
    ! [X2] : k4_xboole_0(k2_zfmisc_1(sK2,X2),k2_zfmisc_1(sK2,k4_xboole_0(X2,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) ),
    inference(forward_demodulation,[],[f155,f82])).

fof(f155,plain,(
    ! [X2] : k3_xboole_0(k2_zfmisc_1(sK2,X2),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK2,X2),k2_zfmisc_1(sK2,k4_xboole_0(X2,sK3))) ),
    inference(superposition,[],[f81,f96])).

fof(f25446,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) ),
    inference(forward_demodulation,[],[f25445,f1379])).

fof(f1379,plain,(
    ! [X1] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X1)) = k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3)) ),
    inference(forward_demodulation,[],[f1363,f81])).

fof(f1363,plain,(
    ! [X1] : k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))) ),
    inference(superposition,[],[f1300,f97])).

fof(f1300,plain,(
    ! [X2] : k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2))) = k2_zfmisc_1(sK2,k3_xboole_0(X2,sK3)) ),
    inference(backward_demodulation,[],[f198,f1297])).

fof(f198,plain,(
    ! [X2] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2))) ),
    inference(superposition,[],[f81,f97])).

fof(f25445,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK2,k3_xboole_0(k4_xboole_0(sK3,sK1),sK3))) ),
    inference(forward_demodulation,[],[f25443,f1297])).

fof(f25443,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)))) ),
    inference(resolution,[],[f25385,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f34,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f25385,plain,(
    r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))) ),
    inference(superposition,[],[f25378,f195])).

fof(f25378,plain,(
    ! [X2] : r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK0,sK2),X2)) ),
    inference(subsumption_resolution,[],[f25373,f524])).

fof(f524,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f522,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f522,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(backward_demodulation,[],[f514,f515])).

fof(f515,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f512,f60])).

fof(f512,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f507,f80])).

fof(f507,plain,(
    r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f502,f241])).

fof(f241,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK2),sK2),sK3) ),
    inference(forward_demodulation,[],[f231,f62])).

fof(f231,plain,(
    k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK2),sK2),sK3) ),
    inference(superposition,[],[f94,f190])).

fof(f190,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK2),sK3) ),
    inference(backward_demodulation,[],[f112,f175])).

fof(f175,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f141,f69])).

fof(f141,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f140,f84])).

fof(f140,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f138,f53])).

fof(f138,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f131,f61])).

fof(f131,plain,(
    ! [X4] : r1_tarski(k2_zfmisc_1(k4_xboole_0(sK2,X4),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f85,f95])).

fof(f95,plain,(
    ! [X1] : k2_zfmisc_1(k4_xboole_0(sK2,X1),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3)) ),
    inference(superposition,[],[f68,f53])).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f112,plain,(
    k2_zfmisc_1(k4_xboole_0(sK2,sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f100,f69])).

fof(f100,plain,(
    k2_zfmisc_1(k4_xboole_0(sK2,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f94,f53])).

fof(f94,plain,(
    ! [X0] : k2_zfmisc_1(k4_xboole_0(X0,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f68,f53])).

fof(f502,plain,
    ( r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK2),sK2),sK3) ),
    inference(superposition,[],[f108,f190])).

fof(f108,plain,(
    ! [X5] :
      ( r1_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1))
      | k2_zfmisc_1(X5,sK3) != k2_zfmisc_1(k4_xboole_0(X5,sK2),sK3) ) ),
    inference(superposition,[],[f87,f94])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f514,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),X1)) ),
    inference(resolution,[],[f512,f93])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f25373,plain,(
    ! [X2] :
      ( r2_hidden(sK7(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK0,sK2),X2)),k1_xboole_0)
      | r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK0,sK2),X2)) ) ),
    inference(superposition,[],[f79,f25189])).

fof(f25189,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK0,sK2),X1)) ),
    inference(forward_demodulation,[],[f25181,f53])).

fof(f25181,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK0,sK2),X1)) ),
    inference(superposition,[],[f24894,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f24894,plain,(
    ! [X7] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k3_xboole_0(sK3,X7)) ),
    inference(superposition,[],[f24178,f81])).

fof(f24178,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK3,X3)) ),
    inference(forward_demodulation,[],[f24177,f62])).

fof(f24177,plain,(
    ! [X3] : k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK3,X3)) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),X3)) ),
    inference(forward_demodulation,[],[f24112,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f24112,plain,(
    ! [X3] : k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK3,X3)) = k4_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),X3)) ),
    inference(backward_demodulation,[],[f4190,f24090])).

fof(f24090,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f24087,f60])).

fof(f24087,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) ),
    inference(subsumption_resolution,[],[f24086,f13113])).

fof(f13113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)))
      | ~ r2_hidden(X0,k4_xboole_0(X1,sK1)) ) ),
    inference(resolution,[],[f13082,f92])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13082,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) ) ),
    inference(subsumption_resolution,[],[f13076,f524])).

fof(f13076,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) ) ),
    inference(superposition,[],[f91,f12979])).

fof(f12979,plain,(
    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f12974,f54])).

fof(f12974,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),sK1) ),
    inference(trivial_inequality_removal,[],[f12973])).

fof(f12973,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),sK1) ),
    inference(superposition,[],[f57,f4195])).

fof(f4195,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),sK1)) ),
    inference(forward_demodulation,[],[f4194,f2188])).

fof(f2188,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,X1),sK2),sK3) ),
    inference(superposition,[],[f1915,f81])).

fof(f1915,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,X1),sK2),sK3) ),
    inference(superposition,[],[f137,f94])).

fof(f137,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK2,X0),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f131,f84])).

fof(f4194,plain,(
    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),sK1)) ),
    inference(forward_demodulation,[],[f4172,f69])).

fof(f4172,plain,(
    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f94,f849])).

fof(f849,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),sK3) ),
    inference(forward_demodulation,[],[f848,f728])).

fof(f728,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK3,sK1),sK1))) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) ),
    inference(forward_demodulation,[],[f727,f342])).

fof(f342,plain,(
    ! [X2,X3] : k3_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK0,X3)) = k2_zfmisc_1(sK0,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f65,f322])).

fof(f322,plain,(
    sK0 = k3_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f316,f61])).

fof(f316,plain,(
    k3_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f81,f306])).

fof(f306,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(subsumption_resolution,[],[f301,f55])).

fof(f301,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f300])).

fof(f300,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f57,f176])).

fof(f176,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK0),sK1) ),
    inference(superposition,[],[f141,f68])).

fof(f727,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK3,sK1),sK1))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))) ),
    inference(forward_demodulation,[],[f726,f82])).

fof(f726,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK3,sK1),sK1))) ),
    inference(forward_demodulation,[],[f708,f291])).

fof(f291,plain,(
    k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK3,sK1),sK1)) ),
    inference(forward_demodulation,[],[f284,f69])).

fof(f284,plain,(
    k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f94,f101])).

fof(f708,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3)) ),
    inference(superposition,[],[f105,f101])).

fof(f105,plain,(
    ! [X2] : k3_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(k4_xboole_0(X2,sK2),sK3)) ),
    inference(superposition,[],[f81,f94])).

fof(f848,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK3,sK1),sK1))) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),sK3) ),
    inference(forward_demodulation,[],[f847,f291])).

fof(f847,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),sK3) ),
    inference(forward_demodulation,[],[f824,f82])).

fof(f824,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3) ),
    inference(superposition,[],[f748,f101])).

fof(f748,plain,(
    ! [X2] : k4_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(k4_xboole_0(X2,sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(X2,sK2),sK3) ),
    inference(backward_demodulation,[],[f105,f746])).

fof(f746,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f716,f81])).

fof(f716,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,sK2)),sK3) ),
    inference(superposition,[],[f105,f68])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f24086,plain,(
    ! [X0] :
      ( r2_hidden(X0,k4_xboole_0(sK3,sK1))
      | ~ r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) ) ),
    inference(subsumption_resolution,[],[f24081,f524])).

fof(f24081,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,k4_xboole_0(sK3,sK1))
      | ~ r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) ) ),
    inference(superposition,[],[f91,f24067])).

fof(f24067,plain,(
    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f24062,f54])).

fof(f24062,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,sK1)) ),
    inference(trivial_inequality_removal,[],[f24061])).

fof(f24061,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f57,f11606])).

fof(f11606,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,sK1))) ),
    inference(backward_demodulation,[],[f7200,f11549])).

fof(f11549,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,X3),X3),sK3) ),
    inference(superposition,[],[f11473,f82])).

fof(f11473,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k3_xboole_0(X1,sK2),X1),sK3) ),
    inference(superposition,[],[f885,f68])).

fof(f885,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,sK2),sK3),k2_zfmisc_1(X0,sK3)) ),
    inference(resolution,[],[f753,f84])).

fof(f753,plain,(
    ! [X5] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X5,sK2),sK3),k2_zfmisc_1(X5,sK3)) ),
    inference(forward_demodulation,[],[f720,f746])).

fof(f720,plain,(
    ! [X5] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(X5,sK3)) ),
    inference(superposition,[],[f85,f105])).

fof(f7200,plain,(
    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2)),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,sK1))) ),
    inference(forward_demodulation,[],[f7160,f69])).

fof(f7160,plain,(
    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2)),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))) ),
    inference(superposition,[],[f285,f849])).

fof(f285,plain,(
    ! [X0] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(sK0,sK2)),sK3) = k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))) ),
    inference(superposition,[],[f68,f101])).

fof(f4190,plain,(
    ! [X3] : k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK3,X3)) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))),k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),X3)) ),
    inference(superposition,[],[f69,f849])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f195,plain,(
    k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f97,f68])).

fof(f101,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK3) ),
    inference(superposition,[],[f94,f69])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26705,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f26680,f54])).

fof(f26680,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    inference(backward_demodulation,[],[f13403,f26668])).

fof(f26668,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f26632,f61])).

fof(f26632,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f81,f25597])).

fof(f13403,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f13397,f55])).

fof(f13397,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f57,f7897])).

fof(f7897,plain,(
    k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f7896,f81])).

fof(f7896,plain,(
    k2_zfmisc_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f7895,f82])).

fof(f7895,plain,(
    k2_zfmisc_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1) ),
    inference(forward_demodulation,[],[f7877,f81])).

fof(f7877,plain,(
    k2_zfmisc_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK1) ),
    inference(superposition,[],[f343,f69])).

fof(f343,plain,(
    ! [X0] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(sK2,sK0)),sK1) = k4_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f68,f149])).

fof(f149,plain,(
    k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f96,f68])).

fof(f28660,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | sK0 = sK2 ),
    inference(forward_demodulation,[],[f28433,f89])).

fof(f28433,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k1_xboole_0)
    | sK0 = sK2 ),
    inference(superposition,[],[f53,f28428])).

fof(f28428,plain,
    ( k1_xboole_0 = sK3
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f28378,f25597])).

fof(f28378,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK2)
    | sK0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f64,f28297])).

fof(f28297,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | k1_xboole_0 = sK3 ),
    inference(trivial_inequality_removal,[],[f28296])).

fof(f28296,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f57,f28092])).

fof(f28092,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    inference(backward_demodulation,[],[f125,f28082])).

fof(f28082,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f27246,f60])).

fof(f27246,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    inference(trivial_inequality_removal,[],[f27235])).

fof(f27235,plain,(
    ! [X0] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK1)
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ) ),
    inference(backward_demodulation,[],[f25947,f27216])).

fof(f27216,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f27215,f53])).

fof(f27215,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f27214,f26668])).

fof(f27214,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    inference(forward_demodulation,[],[f27213,f82])).

fof(f27213,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) ),
    inference(forward_demodulation,[],[f27212,f61])).

fof(f27212,plain,(
    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f27093,f90])).

fof(f27093,plain,(
    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k1_xboole_0,sK3)) ),
    inference(superposition,[],[f26886,f14239])).

fof(f14239,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f14216])).

fof(f14216,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f532,f530])).

fof(f530,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(X4,X5,k1_xboole_0),X4)
      | k1_xboole_0 = k4_xboole_0(X4,X5) ) ),
    inference(forward_demodulation,[],[f529,f515])).

fof(f529,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(X4,X5,k1_xboole_0),X4)
      | k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(X4,X5) ) ),
    inference(forward_demodulation,[],[f517,f515])).

fof(f517,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(X4,X5,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),X4)
      | k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f512,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f532,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK5(X6,X7,k1_xboole_0),X7)
      | k1_xboole_0 = k4_xboole_0(X6,X7) ) ),
    inference(forward_demodulation,[],[f531,f515])).

fof(f531,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK5(X6,X7,k1_xboole_0),X7)
      | k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(X6,X7) ) ),
    inference(forward_demodulation,[],[f518,f515])).

fof(f518,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK5(X6,X7,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),X7)
      | k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f512,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f26886,plain,(
    ! [X2] : k4_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(k4_xboole_0(X2,sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(X2,sK0),sK3) ),
    inference(backward_demodulation,[],[f748,f26883])).

fof(f26883,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k2_zfmisc_1(k3_xboole_0(X1,sK0),sK3) ),
    inference(backward_demodulation,[],[f746,f26881])).

fof(f26881,plain,(
    ! [X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),sK3) = k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK1)) ),
    inference(backward_demodulation,[],[f26813,f26880])).

fof(f26880,plain,(
    ! [X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),sK3) = k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) ),
    inference(forward_demodulation,[],[f26836,f8449])).

fof(f8449,plain,(
    ! [X2,X1] : k2_zfmisc_1(k3_xboole_0(X1,X2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(X2,sK3)) ),
    inference(superposition,[],[f65,f8344])).

fof(f8344,plain,(
    sK3 = k3_xboole_0(sK3,sK3) ),
    inference(forward_demodulation,[],[f8305,f61])).

fof(f8305,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f81,f7989])).

fof(f7989,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(subsumption_resolution,[],[f7988,f55])).

fof(f7988,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(subsumption_resolution,[],[f7962,f54])).

fof(f7962,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(trivial_inequality_removal,[],[f7961])).

fof(f7961,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f57,f3730])).

fof(f3730,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(forward_demodulation,[],[f3662,f90])).

fof(f3662,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f240,f1046])).

fof(f1046,plain,(
    ! [X8] :
      ( k1_xboole_0 = k3_xboole_0(sK2,X8)
      | k1_xboole_0 = k4_xboole_0(sK3,sK3) ) ),
    inference(trivial_inequality_removal,[],[f1045])).

fof(f1045,plain,(
    ! [X8] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(sK2,X8)
      | k1_xboole_0 = k4_xboole_0(sK3,sK3) ) ),
    inference(superposition,[],[f57,f642])).

fof(f642,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,X0),k4_xboole_0(sK3,sK3)) ),
    inference(superposition,[],[f224,f81])).

fof(f224,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,X1),k4_xboole_0(sK3,sK3)) ),
    inference(forward_demodulation,[],[f213,f62])).

fof(f213,plain,(
    ! [X1] : k2_zfmisc_1(k4_xboole_0(sK2,X1),k4_xboole_0(sK3,sK3)) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,k4_xboole_0(sK3,sK3))) ),
    inference(superposition,[],[f68,f187])).

fof(f187,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3)) ),
    inference(backward_demodulation,[],[f160,f175])).

fof(f160,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3)) ),
    inference(forward_demodulation,[],[f147,f69])).

fof(f147,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3)) ),
    inference(superposition,[],[f96,f53])).

fof(f240,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3) ),
    inference(forward_demodulation,[],[f239,f61])).

fof(f239,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3) ),
    inference(forward_demodulation,[],[f229,f81])).

fof(f229,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),sK3) ),
    inference(superposition,[],[f95,f190])).

fof(f26836,plain,(
    ! [X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK3)) = k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) ),
    inference(backward_demodulation,[],[f17724,f26802])).

fof(f17724,plain,(
    ! [X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) = k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f17721,f65])).

fof(f17721,plain,(
    ! [X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(sK1,sK3)) = k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f65,f17687])).

fof(f17687,plain,(
    k3_xboole_0(sK1,sK3) = k3_xboole_0(sK3,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f17686,f61])).

fof(f17686,plain,(
    k4_xboole_0(k3_xboole_0(sK1,sK3),k1_xboole_0) = k3_xboole_0(sK3,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f17649,f82])).

fof(f17649,plain,(
    k4_xboole_0(k3_xboole_0(sK1,sK3),k1_xboole_0) = k3_xboole_0(k3_xboole_0(sK1,sK3),sK3) ),
    inference(superposition,[],[f81,f17612])).

fof(f17612,plain,(
    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3) ),
    inference(subsumption_resolution,[],[f17607,f54])).

fof(f17607,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3) ),
    inference(trivial_inequality_removal,[],[f17606])).

fof(f17606,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3) ),
    inference(superposition,[],[f57,f17583])).

fof(f17583,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK3)) ),
    inference(superposition,[],[f2542,f69])).

fof(f2542,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK3)) ),
    inference(resolution,[],[f2457,f84])).

fof(f2457,plain,(
    r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK3)) ),
    inference(superposition,[],[f753,f335])).

fof(f335,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    inference(forward_demodulation,[],[f334,f82])).

fof(f334,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) ),
    inference(forward_demodulation,[],[f333,f81])).

fof(f333,plain,(
    k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f332,f81])).

fof(f332,plain,(
    k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f324,f69])).

fof(f324,plain,(
    k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f95,f125])).

fof(f26813,plain,(
    ! [X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) = k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK1)) ),
    inference(backward_demodulation,[],[f2818,f26802])).

fof(f2818,plain,(
    ! [X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X1,sK1)) = k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) ),
    inference(forward_demodulation,[],[f2816,f65])).

fof(f2816,plain,(
    ! [X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X1,sK1)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f65,f2646])).

fof(f2646,plain,(
    k3_xboole_0(sK1,sK3) = k3_xboole_0(k3_xboole_0(sK1,sK3),sK1) ),
    inference(forward_demodulation,[],[f2637,f61])).

fof(f2637,plain,(
    k3_xboole_0(k3_xboole_0(sK1,sK3),sK1) = k4_xboole_0(k3_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[],[f81,f2623])).

fof(f2623,plain,(
    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f2618,f54])).

fof(f2618,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1) ),
    inference(trivial_inequality_removal,[],[f2617])).

fof(f2617,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1) ),
    inference(superposition,[],[f57,f2477])).

fof(f2477,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)) ),
    inference(forward_demodulation,[],[f2476,f2356])).

fof(f2356,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k3_xboole_0(X0,sK2),sK2),sK3) ),
    inference(superposition,[],[f2188,f82])).

fof(f2476,plain,(
    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)) ),
    inference(forward_demodulation,[],[f2458,f69])).

fof(f2458,plain,(
    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f94,f335])).

fof(f25947,plain,(
    ! [X0] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK3)
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ) ),
    inference(backward_demodulation,[],[f9711,f25921])).

fof(f25921,plain,(
    k2_zfmisc_1(sK0,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f25859,f61])).

fof(f25859,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK3),k1_xboole_0) ),
    inference(backward_demodulation,[],[f745,f25854])).

fof(f745,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))) ),
    inference(forward_demodulation,[],[f744,f342])).

fof(f744,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(forward_demodulation,[],[f715,f82])).

fof(f715,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))) ),
    inference(superposition,[],[f105,f101])).

fof(f9711,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))
      | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ) ),
    inference(forward_demodulation,[],[f9709,f3095])).

fof(f3095,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f3069,f1938])).

fof(f1938,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) ),
    inference(backward_demodulation,[],[f854,f1936])).

fof(f1936,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f1933,f61])).

fof(f1933,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f731,f1930])).

fof(f1930,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1)) ),
    inference(backward_demodulation,[],[f336,f1915])).

fof(f336,plain,(
    k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1)) ),
    inference(forward_demodulation,[],[f326,f69])).

fof(f326,plain,(
    k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f94,f125])).

fof(f731,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1))) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f730,f342])).

fof(f730,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f729,f82])).

fof(f729,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1))) ),
    inference(forward_demodulation,[],[f709,f336])).

fof(f709,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3)) ),
    inference(superposition,[],[f105,f125])).

fof(f854,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) ),
    inference(forward_demodulation,[],[f853,f731])).

fof(f853,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1))) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) ),
    inference(forward_demodulation,[],[f852,f336])).

fof(f852,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) ),
    inference(forward_demodulation,[],[f826,f82])).

fof(f826,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3) ),
    inference(superposition,[],[f748,f125])).

fof(f3069,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) ),
    inference(superposition,[],[f949,f125])).

fof(f949,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3)) ),
    inference(forward_demodulation,[],[f930,f81])).

fof(f930,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK3) ),
    inference(superposition,[],[f129,f95])).

fof(f129,plain,(
    ! [X2] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X2,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK2,X2),sK3)) ),
    inference(superposition,[],[f81,f95])).

fof(f9709,plain,(
    ! [X0] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))) ) ),
    inference(resolution,[],[f555,f80])).

fof(f555,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))
    | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f554,f335])).

fof(f554,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)
    | r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f553,f82])).

fof(f553,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3)
    | r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f549,f81])).

fof(f549,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))
    | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) ),
    inference(superposition,[],[f132,f125])).

fof(f132,plain,(
    ! [X5] :
      ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X5,sK3))
      | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k4_xboole_0(sK2,X5),sK3) ) ),
    inference(superposition,[],[f87,f95])).

fof(f125,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f95,f69])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f56,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f31337,plain,(
    sK1 = sK3 ),
    inference(forward_demodulation,[],[f31336,f61])).

fof(f31336,plain,(
    sK3 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f31326,f26802])).

fof(f31326,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f81,f31270])).

fof(f31270,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f31263,f54])).

fof(f31263,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f31262])).

fof(f31262,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f57,f28082])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:55:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (3996)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (3992)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (4012)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (3994)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (4004)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (3991)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (4001)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (4016)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (3993)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (4013)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (3990)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (4005)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (4002)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (3995)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (4017)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (4018)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (4006)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (4010)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (3998)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (4006)Refutation not found, incomplete strategy% (4006)------------------------------
% 0.20/0.55  % (4006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (4006)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (4006)Memory used [KB]: 10618
% 0.20/0.55  % (4006)Time elapsed: 0.138 s
% 0.20/0.55  % (4006)------------------------------
% 0.20/0.55  % (4006)------------------------------
% 0.20/0.55  % (4015)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (3999)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (4011)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (4003)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (4019)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (4019)Refutation not found, incomplete strategy% (4019)------------------------------
% 0.20/0.55  % (4019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (4019)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (4019)Memory used [KB]: 1663
% 0.20/0.55  % (4019)Time elapsed: 0.136 s
% 0.20/0.55  % (4019)------------------------------
% 0.20/0.55  % (4019)------------------------------
% 0.20/0.55  % (4007)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (4014)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.56  % (4008)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.56  % (4000)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.56  % (4009)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.56  % (3997)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.08/0.69  % (4108)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.08/0.70  % (4096)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.04/0.83  % (3992)Time limit reached!
% 3.04/0.83  % (3992)------------------------------
% 3.04/0.83  % (3992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.04/0.83  % (3992)Termination reason: Time limit
% 3.04/0.83  
% 3.04/0.83  % (3992)Memory used [KB]: 6780
% 3.04/0.83  % (3992)Time elapsed: 0.414 s
% 3.04/0.83  % (3992)------------------------------
% 3.04/0.83  % (3992)------------------------------
% 3.04/0.84  % (4014)Time limit reached!
% 3.04/0.84  % (4014)------------------------------
% 3.04/0.84  % (4014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.04/0.84  % (4014)Termination reason: Time limit
% 3.04/0.84  
% 3.04/0.84  % (4014)Memory used [KB]: 13048
% 3.04/0.84  % (4014)Time elapsed: 0.426 s
% 3.04/0.84  % (4014)------------------------------
% 3.04/0.84  % (4014)------------------------------
% 3.93/0.92  % (4004)Time limit reached!
% 3.93/0.92  % (4004)------------------------------
% 3.93/0.92  % (4004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.92  % (4004)Termination reason: Time limit
% 3.93/0.92  
% 3.93/0.92  % (4004)Memory used [KB]: 5245
% 3.93/0.92  % (4004)Time elapsed: 0.507 s
% 3.93/0.92  % (4004)------------------------------
% 3.93/0.92  % (4004)------------------------------
% 4.36/0.95  % (3996)Time limit reached!
% 4.36/0.95  % (3996)------------------------------
% 4.36/0.95  % (3996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.95  % (3996)Termination reason: Time limit
% 4.36/0.95  
% 4.36/0.95  % (3996)Memory used [KB]: 15607
% 4.36/0.95  % (3996)Time elapsed: 0.531 s
% 4.36/0.95  % (3996)------------------------------
% 4.36/0.95  % (3996)------------------------------
% 4.36/0.96  % (4202)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.36/0.98  % (4203)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.81/1.04  % (3997)Time limit reached!
% 4.81/1.04  % (3997)------------------------------
% 4.81/1.04  % (3997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.05  % (4243)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.81/1.05  % (3997)Termination reason: Time limit
% 4.81/1.05  
% 4.81/1.05  % (3997)Memory used [KB]: 6140
% 4.81/1.05  % (3997)Time elapsed: 0.630 s
% 4.81/1.05  % (3997)------------------------------
% 4.81/1.05  % (3997)------------------------------
% 4.81/1.08  % (4253)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.24/1.17  % (4254)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.50/1.22  % (3991)Time limit reached!
% 6.50/1.22  % (3991)------------------------------
% 6.50/1.22  % (3991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.70/1.22  % (3991)Termination reason: Time limit
% 6.70/1.22  
% 6.70/1.22  % (3991)Memory used [KB]: 8827
% 6.70/1.22  % (3991)Time elapsed: 0.805 s
% 6.70/1.22  % (3991)------------------------------
% 6.70/1.22  % (3991)------------------------------
% 7.55/1.33  % (3993)Time limit reached!
% 7.55/1.33  % (3993)------------------------------
% 7.55/1.33  % (3993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.55/1.34  % (3993)Termination reason: Time limit
% 7.55/1.34  
% 7.55/1.34  % (3993)Memory used [KB]: 7419
% 7.55/1.34  % (3993)Time elapsed: 0.907 s
% 7.55/1.34  % (3993)------------------------------
% 7.55/1.34  % (3993)------------------------------
% 7.55/1.36  % (4255)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 8.05/1.42  % (4002)Time limit reached!
% 8.05/1.42  % (4002)------------------------------
% 8.05/1.42  % (4002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.05/1.42  % (4002)Termination reason: Time limit
% 8.05/1.42  
% 8.05/1.42  % (4002)Memory used [KB]: 20596
% 8.05/1.42  % (4002)Time elapsed: 1.013 s
% 8.05/1.42  % (4002)------------------------------
% 8.05/1.42  % (4002)------------------------------
% 8.05/1.45  % (4256)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 9.20/1.55  % (4257)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.20/1.58  % (4017)Time limit reached!
% 9.20/1.58  % (4017)------------------------------
% 9.20/1.58  % (4017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.20/1.58  % (4017)Termination reason: Time limit
% 9.20/1.58  % (4017)Termination phase: Saturation
% 9.20/1.58  
% 9.20/1.58  % (4017)Memory used [KB]: 11001
% 9.20/1.58  % (4017)Time elapsed: 1.0000 s
% 9.20/1.58  % (4017)------------------------------
% 9.20/1.58  % (4017)------------------------------
% 9.97/1.63  % (3990)Time limit reached!
% 9.97/1.63  % (3990)------------------------------
% 9.97/1.63  % (3990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.97/1.63  % (3990)Termination reason: Time limit
% 9.97/1.63  
% 9.97/1.63  % (3990)Memory used [KB]: 6780
% 9.97/1.63  % (3990)Time elapsed: 1.212 s
% 9.97/1.63  % (3990)------------------------------
% 9.97/1.63  % (3990)------------------------------
% 10.54/1.68  % (4202)Time limit reached!
% 10.54/1.68  % (4202)------------------------------
% 10.54/1.68  % (4202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.54/1.68  % (4202)Termination reason: Time limit
% 10.54/1.68  % (4202)Termination phase: Saturation
% 10.54/1.68  
% 10.54/1.68  % (4202)Memory used [KB]: 15479
% 10.54/1.68  % (4202)Time elapsed: 0.800 s
% 10.54/1.68  % (4202)------------------------------
% 10.54/1.68  % (4202)------------------------------
% 10.54/1.69  % (4258)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 10.54/1.73  % (3995)Time limit reached!
% 10.54/1.73  % (3995)------------------------------
% 10.54/1.73  % (3995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.54/1.73  % (3995)Termination reason: Time limit
% 10.54/1.73  
% 10.54/1.73  % (3995)Memory used [KB]: 13944
% 10.54/1.73  % (3995)Time elapsed: 1.305 s
% 10.54/1.73  % (3995)------------------------------
% 10.54/1.73  % (3995)------------------------------
% 10.54/1.74  % (4254)Time limit reached!
% 10.54/1.74  % (4254)------------------------------
% 10.54/1.74  % (4254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.54/1.74  % (4254)Termination reason: Time limit
% 10.54/1.74  
% 10.54/1.74  % (4254)Memory used [KB]: 19061
% 10.54/1.74  % (4254)Time elapsed: 0.620 s
% 10.54/1.74  % (4254)------------------------------
% 10.54/1.74  % (4254)------------------------------
% 10.54/1.75  % (4259)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 11.58/1.82  % (4260)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 11.58/1.87  % (4261)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.58/1.87  % (4262)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 12.70/2.03  % (4016)Time limit reached!
% 12.70/2.03  % (4016)------------------------------
% 12.70/2.03  % (4016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.70/2.05  % (4016)Termination reason: Time limit
% 12.70/2.05  
% 12.70/2.05  % (4016)Memory used [KB]: 20084
% 12.70/2.05  % (4016)Time elapsed: 1.620 s
% 12.70/2.05  % (4016)------------------------------
% 12.70/2.05  % (4016)------------------------------
% 14.13/2.16  % (4008)Refutation found. Thanks to Tanya!
% 14.13/2.16  % SZS status Theorem for theBenchmark
% 14.13/2.18  % (4261)Time limit reached!
% 14.13/2.18  % (4261)------------------------------
% 14.13/2.18  % (4261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.13/2.18  % SZS output start Proof for theBenchmark
% 14.13/2.18  fof(f31338,plain,(
% 14.13/2.18    $false),
% 14.13/2.18    inference(subsumption_resolution,[],[f31337,f29876])).
% 14.13/2.18  fof(f29876,plain,(
% 14.13/2.18    sK1 != sK3),
% 14.13/2.18    inference(trivial_inequality_removal,[],[f28663])).
% 14.13/2.18  fof(f28663,plain,(
% 14.13/2.18    sK0 != sK0 | sK1 != sK3),
% 14.13/2.18    inference(backward_demodulation,[],[f56,f28661])).
% 14.13/2.18  fof(f28661,plain,(
% 14.13/2.18    sK0 = sK2),
% 14.13/2.18    inference(subsumption_resolution,[],[f28660,f27721])).
% 14.13/2.18  fof(f27721,plain,(
% 14.13/2.18    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 14.13/2.18    inference(superposition,[],[f26860,f53])).
% 14.13/2.18  fof(f53,plain,(
% 14.13/2.18    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 14.13/2.18    inference(cnf_transformation,[],[f37])).
% 14.13/2.18  fof(f37,plain,(
% 14.13/2.18    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 14.13/2.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f36])).
% 14.13/2.18  fof(f36,plain,(
% 14.13/2.18    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 14.13/2.18    introduced(choice_axiom,[])).
% 14.13/2.18  fof(f29,plain,(
% 14.13/2.18    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 14.13/2.18    inference(flattening,[],[f28])).
% 14.13/2.18  fof(f28,plain,(
% 14.13/2.18    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 14.13/2.18    inference(ennf_transformation,[],[f25])).
% 14.13/2.18  fof(f25,negated_conjecture,(
% 14.13/2.18    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 14.13/2.18    inference(negated_conjecture,[],[f24])).
% 14.13/2.18  fof(f24,conjecture,(
% 14.13/2.18    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 14.13/2.18  fof(f26860,plain,(
% 14.13/2.18    k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 14.13/2.18    inference(backward_demodulation,[],[f26705,f26802])).
% 14.13/2.18  fof(f26802,plain,(
% 14.13/2.18    sK3 = k3_xboole_0(sK1,sK3)),
% 14.13/2.18    inference(forward_demodulation,[],[f26801,f61])).
% 14.13/2.18  fof(f61,plain,(
% 14.13/2.18    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 14.13/2.18    inference(cnf_transformation,[],[f12])).
% 14.13/2.18  fof(f12,axiom,(
% 14.13/2.18    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 14.13/2.18  fof(f26801,plain,(
% 14.13/2.18    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK1,sK3)),
% 14.13/2.18    inference(forward_demodulation,[],[f26755,f82])).
% 14.13/2.18  fof(f82,plain,(
% 14.13/2.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 14.13/2.18    inference(cnf_transformation,[],[f1])).
% 14.13/2.18  fof(f1,axiom,(
% 14.13/2.18    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 14.13/2.18  fof(f26755,plain,(
% 14.13/2.18    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,sK1)),
% 14.13/2.18    inference(superposition,[],[f81,f26496])).
% 14.13/2.18  fof(f26496,plain,(
% 14.13/2.18    k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 14.13/2.18    inference(subsumption_resolution,[],[f26489,f54])).
% 14.13/2.18  fof(f54,plain,(
% 14.13/2.18    k1_xboole_0 != sK0),
% 14.13/2.18    inference(cnf_transformation,[],[f37])).
% 14.13/2.18  fof(f26489,plain,(
% 14.13/2.18    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 14.13/2.18    inference(trivial_inequality_removal,[],[f26488])).
% 14.13/2.18  fof(f26488,plain,(
% 14.13/2.18    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 14.13/2.18    inference(superposition,[],[f57,f25854])).
% 14.13/2.18  fof(f25854,plain,(
% 14.13/2.18    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))),
% 14.13/2.18    inference(forward_demodulation,[],[f25598,f90])).
% 14.13/2.18  fof(f90,plain,(
% 14.13/2.18    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 14.13/2.18    inference(equality_resolution,[],[f58])).
% 14.13/2.18  fof(f58,plain,(
% 14.13/2.18    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 14.13/2.18    inference(cnf_transformation,[],[f39])).
% 14.13/2.18  fof(f39,plain,(
% 14.13/2.18    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 14.13/2.18    inference(flattening,[],[f38])).
% 14.13/2.18  fof(f38,plain,(
% 14.13/2.18    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 14.13/2.18    inference(nnf_transformation,[],[f20])).
% 14.13/2.18  fof(f20,axiom,(
% 14.13/2.18    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 14.13/2.18  fof(f25598,plain,(
% 14.13/2.18    k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))),
% 14.13/2.18    inference(backward_demodulation,[],[f101,f25597])).
% 14.13/2.18  fof(f25597,plain,(
% 14.13/2.18    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 14.13/2.18    inference(subsumption_resolution,[],[f25585,f55])).
% 14.13/2.18  fof(f55,plain,(
% 14.13/2.18    k1_xboole_0 != sK1),
% 14.13/2.18    inference(cnf_transformation,[],[f37])).
% 14.13/2.18  fof(f25585,plain,(
% 14.13/2.18    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 14.13/2.18    inference(trivial_inequality_removal,[],[f25584])).
% 14.13/2.18  fof(f25584,plain,(
% 14.13/2.18    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 14.13/2.18    inference(superposition,[],[f57,f25468])).
% 14.13/2.18  fof(f25468,plain,(
% 14.13/2.18    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 14.13/2.18    inference(backward_demodulation,[],[f195,f25455])).
% 14.13/2.18  fof(f25455,plain,(
% 14.13/2.18    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))),
% 14.13/2.18    inference(resolution,[],[f25447,f60])).
% 14.13/2.18  fof(f60,plain,(
% 14.13/2.18    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 14.13/2.18    inference(cnf_transformation,[],[f41])).
% 14.13/2.18  fof(f41,plain,(
% 14.13/2.18    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 14.13/2.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f40])).
% 14.13/2.18  fof(f40,plain,(
% 14.13/2.18    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 14.13/2.18    introduced(choice_axiom,[])).
% 14.13/2.18  fof(f30,plain,(
% 14.13/2.18    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 14.13/2.18    inference(ennf_transformation,[],[f7])).
% 14.13/2.18  fof(f7,axiom,(
% 14.13/2.18    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 14.13/2.18  fof(f25447,plain,(
% 14.13/2.18    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f25446,f2524])).
% 14.13/2.18  fof(f2524,plain,(
% 14.13/2.18    ( ! [X2] : (k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2)) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(sK3,X2)))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f2523,f82])).
% 14.13/2.18  fof(f2523,plain,(
% 14.13/2.18    ( ! [X2] : (k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2)) = k2_zfmisc_1(sK2,k3_xboole_0(k4_xboole_0(sK3,X2),sK3))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f2501,f61])).
% 14.13/2.18  fof(f2501,plain,(
% 14.13/2.18    ( ! [X2] : (k2_zfmisc_1(sK2,k3_xboole_0(k4_xboole_0(sK3,X2),sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2)),k1_xboole_0)) )),
% 14.13/2.18    inference(superposition,[],[f1301,f2408])).
% 14.13/2.18  fof(f2408,plain,(
% 14.13/2.18    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(k4_xboole_0(sK3,X1),sK3))) )),
% 14.13/2.18    inference(superposition,[],[f265,f96])).
% 14.13/2.18  fof(f96,plain,(
% 14.13/2.18    ( ! [X2] : (k2_zfmisc_1(sK2,k4_xboole_0(X2,sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,X2),k2_zfmisc_1(sK0,sK1))) )),
% 14.13/2.18    inference(superposition,[],[f69,f53])).
% 14.13/2.18  fof(f69,plain,(
% 14.13/2.18    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 14.13/2.18    inference(cnf_transformation,[],[f23])).
% 14.13/2.18  fof(f23,axiom,(
% 14.13/2.18    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 14.13/2.18  fof(f265,plain,(
% 14.13/2.18    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1))) )),
% 14.13/2.18    inference(resolution,[],[f200,f84])).
% 14.13/2.18  fof(f84,plain,(
% 14.13/2.18    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 14.13/2.18    inference(cnf_transformation,[],[f51])).
% 14.13/2.18  fof(f51,plain,(
% 14.13/2.18    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 14.13/2.18    inference(nnf_transformation,[],[f8])).
% 14.13/2.18  fof(f8,axiom,(
% 14.13/2.18    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 14.13/2.18  fof(f200,plain,(
% 14.13/2.18    ( ! [X4] : (r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X4)),k2_zfmisc_1(sK0,sK1))) )),
% 14.13/2.18    inference(superposition,[],[f85,f97])).
% 14.13/2.18  fof(f97,plain,(
% 14.13/2.18    ( ! [X3] : (k2_zfmisc_1(sK2,k4_xboole_0(sK3,X3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X3))) )),
% 14.13/2.18    inference(superposition,[],[f69,f53])).
% 14.13/2.18  fof(f85,plain,(
% 14.13/2.18    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 14.13/2.18    inference(cnf_transformation,[],[f11])).
% 14.13/2.18  fof(f11,axiom,(
% 14.13/2.18    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 14.13/2.18  fof(f1301,plain,(
% 14.13/2.18    ( ! [X2] : (k4_xboole_0(k2_zfmisc_1(sK2,X2),k2_zfmisc_1(sK2,k4_xboole_0(X2,sK3))) = k2_zfmisc_1(sK2,k3_xboole_0(X2,sK3))) )),
% 14.13/2.18    inference(backward_demodulation,[],[f165,f1297])).
% 14.13/2.18  fof(f1297,plain,(
% 14.13/2.18    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f1264,f81])).
% 14.13/2.18  fof(f1264,plain,(
% 14.13/2.18    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,sK3)))) )),
% 14.13/2.18    inference(superposition,[],[f165,f69])).
% 14.13/2.18  fof(f165,plain,(
% 14.13/2.18    ( ! [X2] : (k4_xboole_0(k2_zfmisc_1(sK2,X2),k2_zfmisc_1(sK2,k4_xboole_0(X2,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f155,f82])).
% 14.13/2.18  fof(f155,plain,(
% 14.13/2.18    ( ! [X2] : (k3_xboole_0(k2_zfmisc_1(sK2,X2),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK2,X2),k2_zfmisc_1(sK2,k4_xboole_0(X2,sK3)))) )),
% 14.13/2.18    inference(superposition,[],[f81,f96])).
% 14.13/2.18  fof(f25446,plain,(
% 14.13/2.18    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(sK3,sK1))))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f25445,f1379])).
% 14.13/2.18  fof(f1379,plain,(
% 14.13/2.18    ( ! [X1] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X1)) = k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f1363,f81])).
% 14.13/2.18  fof(f1363,plain,(
% 14.13/2.18    ( ! [X1] : (k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X1)))) )),
% 14.13/2.18    inference(superposition,[],[f1300,f97])).
% 14.13/2.18  fof(f1300,plain,(
% 14.13/2.18    ( ! [X2] : (k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2))) = k2_zfmisc_1(sK2,k3_xboole_0(X2,sK3))) )),
% 14.13/2.18    inference(backward_demodulation,[],[f198,f1297])).
% 14.13/2.18  fof(f198,plain,(
% 14.13/2.18    ( ! [X2] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2)))) )),
% 14.13/2.18    inference(superposition,[],[f81,f97])).
% 14.13/2.18  fof(f25445,plain,(
% 14.13/2.18    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK2,k3_xboole_0(k4_xboole_0(sK3,sK1),sK3)))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f25443,f1297])).
% 14.13/2.18  fof(f25443,plain,(
% 14.13/2.18    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))))) )),
% 14.13/2.18    inference(resolution,[],[f25385,f80])).
% 14.13/2.18  fof(f80,plain,(
% 14.13/2.18    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 14.13/2.18    inference(cnf_transformation,[],[f50])).
% 14.13/2.18  fof(f50,plain,(
% 14.13/2.18    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 14.13/2.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f34,f49])).
% 14.13/2.18  fof(f49,plain,(
% 14.13/2.18    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)))),
% 14.13/2.18    introduced(choice_axiom,[])).
% 14.13/2.18  fof(f34,plain,(
% 14.13/2.18    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 14.13/2.18    inference(ennf_transformation,[],[f27])).
% 14.13/2.18  fof(f27,plain,(
% 14.13/2.18    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 14.13/2.18    inference(rectify,[],[f6])).
% 14.13/2.18  fof(f6,axiom,(
% 14.13/2.18    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 14.13/2.18  fof(f25385,plain,(
% 14.13/2.18    r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)))),
% 14.13/2.18    inference(superposition,[],[f25378,f195])).
% 14.13/2.18  fof(f25378,plain,(
% 14.13/2.18    ( ! [X2] : (r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK0,sK2),X2))) )),
% 14.13/2.18    inference(subsumption_resolution,[],[f25373,f524])).
% 14.13/2.18  fof(f524,plain,(
% 14.13/2.18    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 14.13/2.18    inference(forward_demodulation,[],[f522,f62])).
% 14.13/2.18  fof(f62,plain,(
% 14.13/2.18    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 14.13/2.18    inference(cnf_transformation,[],[f15])).
% 14.13/2.18  fof(f15,axiom,(
% 14.13/2.18    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 14.13/2.18  fof(f522,plain,(
% 14.13/2.18    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1))) )),
% 14.13/2.18    inference(backward_demodulation,[],[f514,f515])).
% 14.13/2.18  fof(f515,plain,(
% 14.13/2.18    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 14.13/2.18    inference(resolution,[],[f512,f60])).
% 14.13/2.18  fof(f512,plain,(
% 14.13/2.18    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)))) )),
% 14.13/2.18    inference(resolution,[],[f507,f80])).
% 14.13/2.18  fof(f507,plain,(
% 14.13/2.18    r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 14.13/2.18    inference(subsumption_resolution,[],[f502,f241])).
% 14.13/2.18  fof(f241,plain,(
% 14.13/2.18    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK2),sK2),sK3)),
% 14.13/2.18    inference(forward_demodulation,[],[f231,f62])).
% 14.13/2.18  fof(f231,plain,(
% 14.13/2.18    k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK2),sK2),sK3)),
% 14.13/2.18    inference(superposition,[],[f94,f190])).
% 14.13/2.18  fof(f190,plain,(
% 14.13/2.18    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK2),sK3)),
% 14.13/2.18    inference(backward_demodulation,[],[f112,f175])).
% 14.13/2.18  fof(f175,plain,(
% 14.13/2.18    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1))),
% 14.13/2.18    inference(superposition,[],[f141,f69])).
% 14.13/2.18  fof(f141,plain,(
% 14.13/2.18    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 14.13/2.18    inference(resolution,[],[f140,f84])).
% 14.13/2.18  fof(f140,plain,(
% 14.13/2.18    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 14.13/2.18    inference(forward_demodulation,[],[f138,f53])).
% 14.13/2.18  fof(f138,plain,(
% 14.13/2.18    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),
% 14.13/2.18    inference(superposition,[],[f131,f61])).
% 14.13/2.18  fof(f131,plain,(
% 14.13/2.18    ( ! [X4] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(sK2,X4),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 14.13/2.18    inference(superposition,[],[f85,f95])).
% 14.13/2.18  fof(f95,plain,(
% 14.13/2.18    ( ! [X1] : (k2_zfmisc_1(k4_xboole_0(sK2,X1),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3))) )),
% 14.13/2.18    inference(superposition,[],[f68,f53])).
% 14.13/2.18  fof(f68,plain,(
% 14.13/2.18    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 14.13/2.18    inference(cnf_transformation,[],[f23])).
% 14.13/2.18  fof(f112,plain,(
% 14.13/2.18    k2_zfmisc_1(k4_xboole_0(sK2,sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1))),
% 14.13/2.18    inference(forward_demodulation,[],[f100,f69])).
% 14.13/2.18  fof(f100,plain,(
% 14.13/2.18    k2_zfmisc_1(k4_xboole_0(sK2,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 14.13/2.18    inference(superposition,[],[f94,f53])).
% 14.13/2.18  fof(f94,plain,(
% 14.13/2.18    ( ! [X0] : (k2_zfmisc_1(k4_xboole_0(X0,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 14.13/2.18    inference(superposition,[],[f68,f53])).
% 14.13/2.18  fof(f502,plain,(
% 14.13/2.18    r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK2),sK2),sK3)),
% 14.13/2.18    inference(superposition,[],[f108,f190])).
% 14.13/2.18  fof(f108,plain,(
% 14.13/2.18    ( ! [X5] : (r1_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1)) | k2_zfmisc_1(X5,sK3) != k2_zfmisc_1(k4_xboole_0(X5,sK2),sK3)) )),
% 14.13/2.18    inference(superposition,[],[f87,f94])).
% 14.13/2.18  fof(f87,plain,(
% 14.13/2.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 14.13/2.18    inference(cnf_transformation,[],[f52])).
% 14.13/2.18  fof(f52,plain,(
% 14.13/2.18    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 14.13/2.18    inference(nnf_transformation,[],[f16])).
% 14.13/2.18  fof(f16,axiom,(
% 14.13/2.18    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 14.13/2.18  fof(f514,plain,(
% 14.13/2.18    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),X1))) )),
% 14.13/2.18    inference(resolution,[],[f512,f93])).
% 14.13/2.18  fof(f93,plain,(
% 14.13/2.18    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 14.13/2.18    inference(equality_resolution,[],[f70])).
% 14.13/2.18  fof(f70,plain,(
% 14.13/2.18    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 14.13/2.18    inference(cnf_transformation,[],[f46])).
% 14.13/2.18  fof(f46,plain,(
% 14.13/2.18    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.13/2.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 14.13/2.18  fof(f45,plain,(
% 14.13/2.18    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 14.13/2.18    introduced(choice_axiom,[])).
% 14.13/2.18  fof(f44,plain,(
% 14.13/2.18    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.13/2.18    inference(rectify,[],[f43])).
% 14.13/2.18  fof(f43,plain,(
% 14.13/2.18    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.13/2.18    inference(flattening,[],[f42])).
% 14.13/2.18  fof(f42,plain,(
% 14.13/2.18    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.13/2.18    inference(nnf_transformation,[],[f2])).
% 14.13/2.18  fof(f2,axiom,(
% 14.13/2.18    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 14.13/2.18  fof(f25373,plain,(
% 14.13/2.18    ( ! [X2] : (r2_hidden(sK7(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK0,sK2),X2)),k1_xboole_0) | r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK0,sK2),X2))) )),
% 14.13/2.18    inference(superposition,[],[f79,f25189])).
% 14.13/2.18  fof(f25189,plain,(
% 14.13/2.18    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK0,sK2),X1))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f25181,f53])).
% 14.13/2.18  fof(f25181,plain,(
% 14.13/2.18    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK0,sK2),X1))) )),
% 14.13/2.18    inference(superposition,[],[f24894,f65])).
% 14.13/2.18  fof(f65,plain,(
% 14.13/2.18    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 14.13/2.18    inference(cnf_transformation,[],[f22])).
% 14.13/2.18  fof(f22,axiom,(
% 14.13/2.18    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 14.13/2.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 14.13/2.18  fof(f24894,plain,(
% 14.13/2.18    ( ! [X7] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k3_xboole_0(sK3,X7))) )),
% 14.13/2.18    inference(superposition,[],[f24178,f81])).
% 14.13/2.18  fof(f24178,plain,(
% 14.13/2.18    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK3,X3))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f24177,f62])).
% 14.13/2.18  fof(f24177,plain,(
% 14.13/2.18    ( ! [X3] : (k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK3,X3)) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),X3))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f24112,f89])).
% 14.13/2.18  fof(f89,plain,(
% 14.13/2.18    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 14.13/2.18    inference(equality_resolution,[],[f59])).
% 14.13/2.18  fof(f59,plain,(
% 14.13/2.18    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 14.13/2.18    inference(cnf_transformation,[],[f39])).
% 14.13/2.18  fof(f24112,plain,(
% 14.13/2.18    ( ! [X3] : (k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK3,X3)) = k4_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),X3))) )),
% 14.13/2.18    inference(backward_demodulation,[],[f4190,f24090])).
% 14.13/2.18  fof(f24090,plain,(
% 14.13/2.18    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))),
% 14.13/2.18    inference(resolution,[],[f24087,f60])).
% 14.13/2.18  fof(f24087,plain,(
% 14.13/2.18    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)))) )),
% 14.13/2.18    inference(subsumption_resolution,[],[f24086,f13113])).
% 14.13/2.18  fof(f13113,plain,(
% 14.13/2.18    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) | ~r2_hidden(X0,k4_xboole_0(X1,sK1))) )),
% 14.13/2.18    inference(resolution,[],[f13082,f92])).
% 14.13/2.18  fof(f92,plain,(
% 14.13/2.18    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 14.13/2.18    inference(equality_resolution,[],[f71])).
% 14.13/2.18  fof(f71,plain,(
% 14.13/2.18    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 14.13/2.18    inference(cnf_transformation,[],[f46])).
% 14.13/2.18  fof(f13082,plain,(
% 14.13/2.18    ( ! [X3] : (r2_hidden(X3,sK1) | ~r2_hidden(X3,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)))) )),
% 14.13/2.18    inference(subsumption_resolution,[],[f13076,f524])).
% 14.13/2.18  fof(f13076,plain,(
% 14.13/2.18    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,sK1) | ~r2_hidden(X3,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)))) )),
% 14.13/2.18    inference(superposition,[],[f91,f12979])).
% 14.13/2.18  fof(f12979,plain,(
% 14.13/2.18    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),sK1)),
% 14.13/2.18    inference(subsumption_resolution,[],[f12974,f54])).
% 14.13/2.18  fof(f12974,plain,(
% 14.13/2.18    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),sK1)),
% 14.13/2.18    inference(trivial_inequality_removal,[],[f12973])).
% 14.13/2.18  fof(f12973,plain,(
% 14.13/2.18    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),sK1)),
% 14.13/2.18    inference(superposition,[],[f57,f4195])).
% 14.13/2.18  fof(f4195,plain,(
% 14.13/2.18    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),sK1))),
% 14.13/2.18    inference(forward_demodulation,[],[f4194,f2188])).
% 14.13/2.18  fof(f2188,plain,(
% 14.13/2.18    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,X1),sK2),sK3)) )),
% 14.13/2.18    inference(superposition,[],[f1915,f81])).
% 14.13/2.18  fof(f1915,plain,(
% 14.13/2.18    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,X1),sK2),sK3)) )),
% 14.13/2.18    inference(superposition,[],[f137,f94])).
% 14.13/2.18  fof(f137,plain,(
% 14.13/2.18    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK2,X0),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 14.13/2.18    inference(resolution,[],[f131,f84])).
% 14.13/2.18  fof(f4194,plain,(
% 14.13/2.18    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),sK1))),
% 14.13/2.18    inference(forward_demodulation,[],[f4172,f69])).
% 14.13/2.18  fof(f4172,plain,(
% 14.13/2.18    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))),k2_zfmisc_1(sK0,sK1))),
% 14.13/2.18    inference(superposition,[],[f94,f849])).
% 14.13/2.18  fof(f849,plain,(
% 14.13/2.18    k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),sK3)),
% 14.13/2.18    inference(forward_demodulation,[],[f848,f728])).
% 14.13/2.18  fof(f728,plain,(
% 14.13/2.18    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK3,sK1),sK1))) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)))),
% 14.13/2.18    inference(forward_demodulation,[],[f727,f342])).
% 14.13/2.18  fof(f342,plain,(
% 14.13/2.18    ( ! [X2,X3] : (k3_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK0,X3)) = k2_zfmisc_1(sK0,k3_xboole_0(X2,X3))) )),
% 14.13/2.18    inference(superposition,[],[f65,f322])).
% 14.13/2.18  fof(f322,plain,(
% 14.13/2.18    sK0 = k3_xboole_0(sK0,sK0)),
% 14.13/2.18    inference(forward_demodulation,[],[f316,f61])).
% 14.13/2.18  fof(f316,plain,(
% 14.13/2.18    k3_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k1_xboole_0)),
% 14.13/2.18    inference(superposition,[],[f81,f306])).
% 14.13/2.18  fof(f306,plain,(
% 14.13/2.18    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 14.13/2.18    inference(subsumption_resolution,[],[f301,f55])).
% 14.13/2.18  fof(f301,plain,(
% 14.13/2.18    k1_xboole_0 = k4_xboole_0(sK0,sK0) | k1_xboole_0 = sK1),
% 14.13/2.18    inference(trivial_inequality_removal,[],[f300])).
% 14.13/2.18  fof(f300,plain,(
% 14.13/2.18    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK0) | k1_xboole_0 = sK1),
% 14.13/2.18    inference(superposition,[],[f57,f176])).
% 14.13/2.18  fof(f176,plain,(
% 14.13/2.18    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK0),sK1)),
% 14.13/2.18    inference(superposition,[],[f141,f68])).
% 14.13/2.18  fof(f727,plain,(
% 14.13/2.18    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK3,sK1),sK1))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)))),
% 14.13/2.18    inference(forward_demodulation,[],[f726,f82])).
% 14.13/2.18  fof(f726,plain,(
% 14.13/2.18    k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK3,sK1),sK1)))),
% 14.13/2.18    inference(forward_demodulation,[],[f708,f291])).
% 14.13/2.18  fof(f291,plain,(
% 14.13/2.18    k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK3,sK1),sK1))),
% 14.13/2.18    inference(forward_demodulation,[],[f284,f69])).
% 14.13/2.18  fof(f284,plain,(
% 14.13/2.18    k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1))),
% 14.13/2.18    inference(superposition,[],[f94,f101])).
% 14.13/2.18  fof(f708,plain,(
% 14.13/2.18    k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3))),
% 14.13/2.18    inference(superposition,[],[f105,f101])).
% 14.13/2.18  fof(f105,plain,(
% 14.13/2.18    ( ! [X2] : (k3_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(k4_xboole_0(X2,sK2),sK3))) )),
% 14.13/2.18    inference(superposition,[],[f81,f94])).
% 14.13/2.18  fof(f848,plain,(
% 14.13/2.18    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK3,sK1),sK1))) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),sK3)),
% 14.13/2.18    inference(forward_demodulation,[],[f847,f291])).
% 14.13/2.18  fof(f847,plain,(
% 14.13/2.18    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),sK3)),
% 14.13/2.18    inference(forward_demodulation,[],[f824,f82])).
% 14.13/2.18  fof(f824,plain,(
% 14.13/2.18    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(sK0,sK2),sK2),sK3)),
% 14.13/2.18    inference(superposition,[],[f748,f101])).
% 14.13/2.18  fof(f748,plain,(
% 14.13/2.18    ( ! [X2] : (k4_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(k4_xboole_0(X2,sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(X2,sK2),sK3)) )),
% 14.13/2.18    inference(backward_demodulation,[],[f105,f746])).
% 14.13/2.18  fof(f746,plain,(
% 14.13/2.18    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 14.13/2.18    inference(forward_demodulation,[],[f716,f81])).
% 14.13/2.18  fof(f716,plain,(
% 14.13/2.18    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,sK2)),sK3)) )),
% 14.13/2.18    inference(superposition,[],[f105,f68])).
% 14.13/2.18  fof(f91,plain,(
% 14.13/2.18    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 14.13/2.18    inference(equality_resolution,[],[f72])).
% 14.13/2.18  fof(f72,plain,(
% 14.13/2.18    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 14.13/2.18    inference(cnf_transformation,[],[f46])).
% 14.13/2.18  fof(f24086,plain,(
% 14.13/2.18    ( ! [X0] : (r2_hidden(X0,k4_xboole_0(sK3,sK1)) | ~r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)))) )),
% 14.13/2.18    inference(subsumption_resolution,[],[f24081,f524])).
% 14.13/2.18  fof(f24081,plain,(
% 14.13/2.18    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,k4_xboole_0(sK3,sK1)) | ~r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)))) )),
% 14.13/2.18    inference(superposition,[],[f91,f24067])).
% 14.13/2.18  fof(f24067,plain,(
% 14.13/2.18    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,sK1))),
% 14.13/2.18    inference(subsumption_resolution,[],[f24062,f54])).
% 14.13/2.18  fof(f24062,plain,(
% 14.13/2.18    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,sK1))),
% 14.13/2.18    inference(trivial_inequality_removal,[],[f24061])).
% 14.13/2.18  fof(f24061,plain,(
% 14.13/2.18    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,sK1))),
% 14.13/2.18    inference(superposition,[],[f57,f11606])).
% 14.13/2.18  fof(f11606,plain,(
% 14.13/2.18    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,sK1)))),
% 14.13/2.18    inference(backward_demodulation,[],[f7200,f11549])).
% 14.13/2.18  fof(f11549,plain,(
% 14.13/2.18    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,X3),X3),sK3)) )),
% 14.13/2.18    inference(superposition,[],[f11473,f82])).
% 14.13/2.19  fof(f11473,plain,(
% 14.13/2.19    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k3_xboole_0(X1,sK2),X1),sK3)) )),
% 14.13/2.19    inference(superposition,[],[f885,f68])).
% 14.13/2.19  fof(f885,plain,(
% 14.13/2.19    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,sK2),sK3),k2_zfmisc_1(X0,sK3))) )),
% 14.13/2.19    inference(resolution,[],[f753,f84])).
% 14.13/2.19  fof(f753,plain,(
% 14.13/2.19    ( ! [X5] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X5,sK2),sK3),k2_zfmisc_1(X5,sK3))) )),
% 14.13/2.19    inference(forward_demodulation,[],[f720,f746])).
% 14.13/2.19  fof(f720,plain,(
% 14.13/2.19    ( ! [X5] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(X5,sK3))) )),
% 14.13/2.19    inference(superposition,[],[f85,f105])).
% 14.13/2.19  fof(f7200,plain,(
% 14.13/2.19    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2)),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,sK1)))),
% 14.13/2.19    inference(forward_demodulation,[],[f7160,f69])).
% 14.13/2.19  fof(f7160,plain,(
% 14.13/2.19    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2)),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)))),
% 14.13/2.19    inference(superposition,[],[f285,f849])).
% 14.13/2.19  fof(f285,plain,(
% 14.13/2.19    ( ! [X0] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(sK0,sK2)),sK3) = k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)))) )),
% 14.13/2.19    inference(superposition,[],[f68,f101])).
% 14.13/2.19  fof(f4190,plain,(
% 14.13/2.19    ( ! [X3] : (k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK3,X3)) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))),k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK0,sK2)),X3))) )),
% 14.13/2.19    inference(superposition,[],[f69,f849])).
% 14.13/2.19  fof(f79,plain,(
% 14.13/2.19    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 14.13/2.19    inference(cnf_transformation,[],[f50])).
% 14.13/2.19  fof(f195,plain,(
% 14.13/2.19    k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))),
% 14.13/2.19    inference(superposition,[],[f97,f68])).
% 14.13/2.19  fof(f101,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK3)),
% 14.13/2.19    inference(superposition,[],[f94,f69])).
% 14.13/2.19  fof(f57,plain,(
% 14.13/2.19    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 14.13/2.19    inference(cnf_transformation,[],[f39])).
% 14.13/2.19  fof(f81,plain,(
% 14.13/2.19    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 14.13/2.19    inference(cnf_transformation,[],[f14])).
% 14.13/2.19  fof(f14,axiom,(
% 14.13/2.19    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 14.13/2.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 14.13/2.19  fof(f26705,plain,(
% 14.13/2.19    k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 14.13/2.19    inference(subsumption_resolution,[],[f26680,f54])).
% 14.13/2.19  fof(f26680,plain,(
% 14.13/2.19    k1_xboole_0 = sK0 | k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 14.13/2.19    inference(backward_demodulation,[],[f13403,f26668])).
% 14.13/2.19  fof(f26668,plain,(
% 14.13/2.19    sK0 = k3_xboole_0(sK0,sK2)),
% 14.13/2.19    inference(forward_demodulation,[],[f26632,f61])).
% 14.13/2.19  fof(f26632,plain,(
% 14.13/2.19    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2)),
% 14.13/2.19    inference(superposition,[],[f81,f25597])).
% 14.13/2.19  fof(f13403,plain,(
% 14.13/2.19    k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 14.13/2.19    inference(subsumption_resolution,[],[f13397,f55])).
% 14.13/2.19  fof(f13397,plain,(
% 14.13/2.19    k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 14.13/2.19    inference(superposition,[],[f57,f7897])).
% 14.13/2.19  fof(f7897,plain,(
% 14.13/2.19    k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 14.13/2.19    inference(forward_demodulation,[],[f7896,f81])).
% 14.13/2.19  fof(f7896,plain,(
% 14.13/2.19    k2_zfmisc_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 14.13/2.19    inference(forward_demodulation,[],[f7895,f82])).
% 14.13/2.19  fof(f7895,plain,(
% 14.13/2.19    k2_zfmisc_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1)),
% 14.13/2.19    inference(forward_demodulation,[],[f7877,f81])).
% 14.13/2.19  fof(f7877,plain,(
% 14.13/2.19    k2_zfmisc_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK1)),
% 14.13/2.19    inference(superposition,[],[f343,f69])).
% 14.13/2.19  fof(f343,plain,(
% 14.13/2.19    ( ! [X0] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(sK2,sK0)),sK1) = k4_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3)))) )),
% 14.13/2.19    inference(superposition,[],[f68,f149])).
% 14.13/2.19  fof(f149,plain,(
% 14.13/2.19    k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3))),
% 14.13/2.19    inference(superposition,[],[f96,f68])).
% 14.13/2.19  fof(f28660,plain,(
% 14.13/2.19    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | sK0 = sK2),
% 14.13/2.19    inference(forward_demodulation,[],[f28433,f89])).
% 14.13/2.19  fof(f28433,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k1_xboole_0) | sK0 = sK2),
% 14.13/2.19    inference(superposition,[],[f53,f28428])).
% 14.13/2.19  fof(f28428,plain,(
% 14.13/2.19    k1_xboole_0 = sK3 | sK0 = sK2),
% 14.13/2.19    inference(subsumption_resolution,[],[f28378,f25597])).
% 14.13/2.19  fof(f28378,plain,(
% 14.13/2.19    k1_xboole_0 != k4_xboole_0(sK0,sK2) | sK0 = sK2 | k1_xboole_0 = sK3),
% 14.13/2.19    inference(superposition,[],[f64,f28297])).
% 14.13/2.19  fof(f28297,plain,(
% 14.13/2.19    k1_xboole_0 = k4_xboole_0(sK2,sK0) | k1_xboole_0 = sK3),
% 14.13/2.19    inference(trivial_inequality_removal,[],[f28296])).
% 14.13/2.19  fof(f28296,plain,(
% 14.13/2.19    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK2,sK0) | k1_xboole_0 = sK3),
% 14.13/2.19    inference(superposition,[],[f57,f28092])).
% 14.13/2.19  fof(f28092,plain,(
% 14.13/2.19    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 14.13/2.19    inference(backward_demodulation,[],[f125,f28082])).
% 14.13/2.19  fof(f28082,plain,(
% 14.13/2.19    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 14.13/2.19    inference(resolution,[],[f27246,f60])).
% 14.13/2.19  fof(f27246,plain,(
% 14.13/2.19    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))) )),
% 14.13/2.19    inference(trivial_inequality_removal,[],[f27235])).
% 14.13/2.19  fof(f27235,plain,(
% 14.13/2.19    ( ! [X0] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK1) | ~r2_hidden(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))) )),
% 14.13/2.19    inference(backward_demodulation,[],[f25947,f27216])).
% 14.13/2.19  fof(f27216,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f27215,f53])).
% 14.13/2.19  fof(f27215,plain,(
% 14.13/2.19    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f27214,f26668])).
% 14.13/2.19  fof(f27214,plain,(
% 14.13/2.19    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f27213,f82])).
% 14.13/2.19  fof(f27213,plain,(
% 14.13/2.19    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f27212,f61])).
% 14.13/2.19  fof(f27212,plain,(
% 14.13/2.19    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k1_xboole_0)),
% 14.13/2.19    inference(forward_demodulation,[],[f27093,f90])).
% 14.13/2.19  fof(f27093,plain,(
% 14.13/2.19    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k1_xboole_0,sK3))),
% 14.13/2.19    inference(superposition,[],[f26886,f14239])).
% 14.13/2.19  fof(f14239,plain,(
% 14.13/2.19    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 14.13/2.19    inference(duplicate_literal_removal,[],[f14216])).
% 14.13/2.19  fof(f14216,plain,(
% 14.13/2.19    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 14.13/2.19    inference(resolution,[],[f532,f530])).
% 14.13/2.19  fof(f530,plain,(
% 14.13/2.19    ( ! [X4,X5] : (r2_hidden(sK5(X4,X5,k1_xboole_0),X4) | k1_xboole_0 = k4_xboole_0(X4,X5)) )),
% 14.13/2.19    inference(forward_demodulation,[],[f529,f515])).
% 14.13/2.19  fof(f529,plain,(
% 14.13/2.19    ( ! [X4,X5] : (r2_hidden(sK5(X4,X5,k1_xboole_0),X4) | k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(X4,X5)) )),
% 14.13/2.19    inference(forward_demodulation,[],[f517,f515])).
% 14.13/2.19  fof(f517,plain,(
% 14.13/2.19    ( ! [X4,X5] : (r2_hidden(sK5(X4,X5,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),X4) | k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(X4,X5)) )),
% 14.13/2.19    inference(resolution,[],[f512,f73])).
% 14.13/2.19  fof(f73,plain,(
% 14.13/2.19    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 14.13/2.19    inference(cnf_transformation,[],[f46])).
% 14.13/2.19  fof(f532,plain,(
% 14.13/2.19    ( ! [X6,X7] : (~r2_hidden(sK5(X6,X7,k1_xboole_0),X7) | k1_xboole_0 = k4_xboole_0(X6,X7)) )),
% 14.13/2.19    inference(forward_demodulation,[],[f531,f515])).
% 14.13/2.19  fof(f531,plain,(
% 14.13/2.19    ( ! [X6,X7] : (~r2_hidden(sK5(X6,X7,k1_xboole_0),X7) | k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(X6,X7)) )),
% 14.13/2.19    inference(forward_demodulation,[],[f518,f515])).
% 14.13/2.19  fof(f518,plain,(
% 14.13/2.19    ( ! [X6,X7] : (~r2_hidden(sK5(X6,X7,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),X7) | k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(X6,X7)) )),
% 14.13/2.19    inference(resolution,[],[f512,f74])).
% 14.13/2.19  fof(f74,plain,(
% 14.13/2.19    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2) )),
% 14.13/2.19    inference(cnf_transformation,[],[f46])).
% 14.13/2.19  fof(f26886,plain,(
% 14.13/2.19    ( ! [X2] : (k4_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(k4_xboole_0(X2,sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(X2,sK0),sK3)) )),
% 14.13/2.19    inference(backward_demodulation,[],[f748,f26883])).
% 14.13/2.19  fof(f26883,plain,(
% 14.13/2.19    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k2_zfmisc_1(k3_xboole_0(X1,sK0),sK3)) )),
% 14.13/2.19    inference(backward_demodulation,[],[f746,f26881])).
% 14.13/2.19  fof(f26881,plain,(
% 14.13/2.19    ( ! [X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),sK3) = k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK1))) )),
% 14.13/2.19    inference(backward_demodulation,[],[f26813,f26880])).
% 14.13/2.19  fof(f26880,plain,(
% 14.13/2.19    ( ! [X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),sK3) = k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))) )),
% 14.13/2.19    inference(forward_demodulation,[],[f26836,f8449])).
% 14.13/2.19  fof(f8449,plain,(
% 14.13/2.19    ( ! [X2,X1] : (k2_zfmisc_1(k3_xboole_0(X1,X2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(X2,sK3))) )),
% 14.13/2.19    inference(superposition,[],[f65,f8344])).
% 14.13/2.19  fof(f8344,plain,(
% 14.13/2.19    sK3 = k3_xboole_0(sK3,sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f8305,f61])).
% 14.13/2.19  fof(f8305,plain,(
% 14.13/2.19    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,sK3)),
% 14.13/2.19    inference(superposition,[],[f81,f7989])).
% 14.13/2.19  fof(f7989,plain,(
% 14.13/2.19    k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 14.13/2.19    inference(subsumption_resolution,[],[f7988,f55])).
% 14.13/2.19  fof(f7988,plain,(
% 14.13/2.19    k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 14.13/2.19    inference(subsumption_resolution,[],[f7962,f54])).
% 14.13/2.19  fof(f7962,plain,(
% 14.13/2.19    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 14.13/2.19    inference(trivial_inequality_removal,[],[f7961])).
% 14.13/2.19  fof(f7961,plain,(
% 14.13/2.19    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 14.13/2.19    inference(superposition,[],[f57,f3730])).
% 14.13/2.19  fof(f3730,plain,(
% 14.13/2.19    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f3662,f90])).
% 14.13/2.19  fof(f3662,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3) | k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 14.13/2.19    inference(superposition,[],[f240,f1046])).
% 14.13/2.19  fof(f1046,plain,(
% 14.13/2.19    ( ! [X8] : (k1_xboole_0 = k3_xboole_0(sK2,X8) | k1_xboole_0 = k4_xboole_0(sK3,sK3)) )),
% 14.13/2.19    inference(trivial_inequality_removal,[],[f1045])).
% 14.13/2.19  fof(f1045,plain,(
% 14.13/2.19    ( ! [X8] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK2,X8) | k1_xboole_0 = k4_xboole_0(sK3,sK3)) )),
% 14.13/2.19    inference(superposition,[],[f57,f642])).
% 14.13/2.19  fof(f642,plain,(
% 14.13/2.19    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,X0),k4_xboole_0(sK3,sK3))) )),
% 14.13/2.19    inference(superposition,[],[f224,f81])).
% 14.13/2.19  fof(f224,plain,(
% 14.13/2.19    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,X1),k4_xboole_0(sK3,sK3))) )),
% 14.13/2.19    inference(forward_demodulation,[],[f213,f62])).
% 14.13/2.19  fof(f213,plain,(
% 14.13/2.19    ( ! [X1] : (k2_zfmisc_1(k4_xboole_0(sK2,X1),k4_xboole_0(sK3,sK3)) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,k4_xboole_0(sK3,sK3)))) )),
% 14.13/2.19    inference(superposition,[],[f68,f187])).
% 14.13/2.19  fof(f187,plain,(
% 14.13/2.19    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3))),
% 14.13/2.19    inference(backward_demodulation,[],[f160,f175])).
% 14.13/2.19  fof(f160,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3))),
% 14.13/2.19    inference(forward_demodulation,[],[f147,f69])).
% 14.13/2.19  fof(f147,plain,(
% 14.13/2.19    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3))),
% 14.13/2.19    inference(superposition,[],[f96,f53])).
% 14.13/2.19  fof(f240,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f239,f61])).
% 14.13/2.19  fof(f239,plain,(
% 14.13/2.19    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f229,f81])).
% 14.13/2.19  fof(f229,plain,(
% 14.13/2.19    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),sK3)),
% 14.13/2.19    inference(superposition,[],[f95,f190])).
% 14.13/2.19  fof(f26836,plain,(
% 14.13/2.19    ( ! [X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK3)) = k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))) )),
% 14.13/2.19    inference(backward_demodulation,[],[f17724,f26802])).
% 14.13/2.19  fof(f17724,plain,(
% 14.13/2.19    ( ! [X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) = k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,k3_xboole_0(sK1,sK3)))) )),
% 14.13/2.19    inference(forward_demodulation,[],[f17721,f65])).
% 14.13/2.19  fof(f17721,plain,(
% 14.13/2.19    ( ! [X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(sK1,sK3)) = k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,k3_xboole_0(sK1,sK3)))) )),
% 14.13/2.19    inference(superposition,[],[f65,f17687])).
% 14.13/2.19  fof(f17687,plain,(
% 14.13/2.19    k3_xboole_0(sK1,sK3) = k3_xboole_0(sK3,k3_xboole_0(sK1,sK3))),
% 14.13/2.19    inference(forward_demodulation,[],[f17686,f61])).
% 14.13/2.19  fof(f17686,plain,(
% 14.13/2.19    k4_xboole_0(k3_xboole_0(sK1,sK3),k1_xboole_0) = k3_xboole_0(sK3,k3_xboole_0(sK1,sK3))),
% 14.13/2.19    inference(forward_demodulation,[],[f17649,f82])).
% 14.13/2.19  fof(f17649,plain,(
% 14.13/2.19    k4_xboole_0(k3_xboole_0(sK1,sK3),k1_xboole_0) = k3_xboole_0(k3_xboole_0(sK1,sK3),sK3)),
% 14.13/2.19    inference(superposition,[],[f81,f17612])).
% 14.13/2.19  fof(f17612,plain,(
% 14.13/2.19    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3)),
% 14.13/2.19    inference(subsumption_resolution,[],[f17607,f54])).
% 14.13/2.19  fof(f17607,plain,(
% 14.13/2.19    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3)),
% 14.13/2.19    inference(trivial_inequality_removal,[],[f17606])).
% 14.13/2.19  fof(f17606,plain,(
% 14.13/2.19    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3)),
% 14.13/2.19    inference(superposition,[],[f57,f17583])).
% 14.13/2.19  fof(f17583,plain,(
% 14.13/2.19    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK3))),
% 14.13/2.19    inference(superposition,[],[f2542,f69])).
% 14.13/2.19  fof(f2542,plain,(
% 14.13/2.19    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK3))),
% 14.13/2.19    inference(resolution,[],[f2457,f84])).
% 14.13/2.19  fof(f2457,plain,(
% 14.13/2.19    r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK3))),
% 14.13/2.19    inference(superposition,[],[f753,f335])).
% 14.13/2.19  fof(f335,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f334,f82])).
% 14.13/2.19  fof(f334,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f333,f81])).
% 14.13/2.19  fof(f333,plain,(
% 14.13/2.19    k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 14.13/2.19    inference(forward_demodulation,[],[f332,f81])).
% 14.13/2.19  fof(f332,plain,(
% 14.13/2.19    k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))),
% 14.13/2.19    inference(forward_demodulation,[],[f324,f69])).
% 14.13/2.19  fof(f324,plain,(
% 14.13/2.19    k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))),
% 14.13/2.19    inference(superposition,[],[f95,f125])).
% 14.13/2.19  fof(f26813,plain,(
% 14.13/2.19    ( ! [X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) = k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK1))) )),
% 14.13/2.19    inference(backward_demodulation,[],[f2818,f26802])).
% 14.13/2.19  fof(f2818,plain,(
% 14.13/2.19    ( ! [X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X1,sK1)) = k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))) )),
% 14.13/2.19    inference(forward_demodulation,[],[f2816,f65])).
% 14.13/2.19  fof(f2816,plain,(
% 14.13/2.19    ( ! [X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X1,sK1)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(sK1,sK3))) )),
% 14.13/2.19    inference(superposition,[],[f65,f2646])).
% 14.13/2.19  fof(f2646,plain,(
% 14.13/2.19    k3_xboole_0(sK1,sK3) = k3_xboole_0(k3_xboole_0(sK1,sK3),sK1)),
% 14.13/2.19    inference(forward_demodulation,[],[f2637,f61])).
% 14.13/2.19  fof(f2637,plain,(
% 14.13/2.19    k3_xboole_0(k3_xboole_0(sK1,sK3),sK1) = k4_xboole_0(k3_xboole_0(sK1,sK3),k1_xboole_0)),
% 14.13/2.19    inference(superposition,[],[f81,f2623])).
% 14.13/2.19  fof(f2623,plain,(
% 14.13/2.19    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)),
% 14.13/2.19    inference(subsumption_resolution,[],[f2618,f54])).
% 14.13/2.19  fof(f2618,plain,(
% 14.13/2.19    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)),
% 14.13/2.19    inference(trivial_inequality_removal,[],[f2617])).
% 14.13/2.19  fof(f2617,plain,(
% 14.13/2.19    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)),
% 14.13/2.19    inference(superposition,[],[f57,f2477])).
% 14.13/2.19  fof(f2477,plain,(
% 14.13/2.19    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK1))),
% 14.13/2.19    inference(forward_demodulation,[],[f2476,f2356])).
% 14.13/2.19  fof(f2356,plain,(
% 14.13/2.19    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k3_xboole_0(X0,sK2),sK2),sK3)) )),
% 14.13/2.19    inference(superposition,[],[f2188,f82])).
% 14.13/2.19  fof(f2476,plain,(
% 14.13/2.19    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK1))),
% 14.13/2.19    inference(forward_demodulation,[],[f2458,f69])).
% 14.13/2.19  fof(f2458,plain,(
% 14.13/2.19    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))),
% 14.13/2.19    inference(superposition,[],[f94,f335])).
% 14.13/2.19  fof(f25947,plain,(
% 14.13/2.19    ( ! [X0] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK3) | ~r2_hidden(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))) )),
% 14.13/2.19    inference(backward_demodulation,[],[f9711,f25921])).
% 14.13/2.19  fof(f25921,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 14.13/2.19    inference(forward_demodulation,[],[f25859,f61])).
% 14.13/2.19  fof(f25859,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK3),k1_xboole_0)),
% 14.13/2.19    inference(backward_demodulation,[],[f745,f25854])).
% 14.13/2.19  fof(f745,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)))),
% 14.13/2.19    inference(forward_demodulation,[],[f744,f342])).
% 14.13/2.19  fof(f744,plain,(
% 14.13/2.19    k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 14.13/2.19    inference(forward_demodulation,[],[f715,f82])).
% 14.13/2.19  fof(f715,plain,(
% 14.13/2.19    k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)))),
% 14.13/2.19    inference(superposition,[],[f105,f101])).
% 14.13/2.19  fof(f9711,plain,(
% 14.13/2.19    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) )),
% 14.13/2.19    inference(forward_demodulation,[],[f9709,f3095])).
% 14.13/2.19  fof(f3095,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))),
% 14.13/2.19    inference(forward_demodulation,[],[f3069,f1938])).
% 14.13/2.19  fof(f1938,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3)),
% 14.13/2.19    inference(backward_demodulation,[],[f854,f1936])).
% 14.13/2.19  fof(f1936,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK1,sK3)))),
% 14.13/2.19    inference(forward_demodulation,[],[f1933,f61])).
% 14.13/2.19  fof(f1933,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k1_xboole_0)),
% 14.13/2.19    inference(backward_demodulation,[],[f731,f1930])).
% 14.13/2.19  fof(f1930,plain,(
% 14.13/2.19    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1))),
% 14.13/2.19    inference(backward_demodulation,[],[f336,f1915])).
% 14.13/2.19  fof(f336,plain,(
% 14.13/2.19    k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1))),
% 14.13/2.19    inference(forward_demodulation,[],[f326,f69])).
% 14.13/2.19  fof(f326,plain,(
% 14.13/2.19    k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))),
% 14.13/2.19    inference(superposition,[],[f94,f125])).
% 14.13/2.19  fof(f731,plain,(
% 14.13/2.19    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1))) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK1,sK3)))),
% 14.13/2.19    inference(forward_demodulation,[],[f730,f342])).
% 14.13/2.19  fof(f730,plain,(
% 14.13/2.19    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))),
% 14.13/2.19    inference(forward_demodulation,[],[f729,f82])).
% 14.13/2.19  fof(f729,plain,(
% 14.13/2.19    k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1)))),
% 14.13/2.19    inference(forward_demodulation,[],[f709,f336])).
% 14.13/2.19  fof(f709,plain,(
% 14.13/2.19    k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3))),
% 14.13/2.19    inference(superposition,[],[f105,f125])).
% 14.13/2.19  fof(f854,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f853,f731])).
% 14.13/2.19  fof(f853,plain,(
% 14.13/2.19    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),sK1))) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f852,f336])).
% 14.13/2.19  fof(f852,plain,(
% 14.13/2.19    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3)),
% 14.13/2.19    inference(forward_demodulation,[],[f826,f82])).
% 14.13/2.19  fof(f826,plain,(
% 14.13/2.19    k4_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(sK2,sK0),sK2),sK3)),
% 14.13/2.19    inference(superposition,[],[f748,f125])).
% 14.13/2.19  fof(f3069,plain,(
% 14.13/2.19    k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3)),
% 14.13/2.19    inference(superposition,[],[f949,f125])).
% 14.13/2.19  fof(f949,plain,(
% 14.13/2.19    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3))) )),
% 14.13/2.19    inference(forward_demodulation,[],[f930,f81])).
% 14.13/2.19  fof(f930,plain,(
% 14.13/2.19    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK3)) )),
% 14.13/2.19    inference(superposition,[],[f129,f95])).
% 14.13/2.19  fof(f129,plain,(
% 14.13/2.19    ( ! [X2] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X2,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK2,X2),sK3))) )),
% 14.13/2.19    inference(superposition,[],[f81,f95])).
% 14.13/2.19  fof(f9709,plain,(
% 14.13/2.19    ( ! [X0] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))))) )),
% 14.13/2.19    inference(resolution,[],[f555,f80])).
% 14.13/2.19  fof(f555,plain,(
% 14.13/2.19    r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 14.13/2.19    inference(forward_demodulation,[],[f554,f335])).
% 14.13/2.19  fof(f554,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) | r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))),
% 14.13/2.19    inference(forward_demodulation,[],[f553,f82])).
% 14.13/2.19  fof(f553,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) | r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))),
% 14.13/2.19    inference(forward_demodulation,[],[f549,f81])).
% 14.13/2.19  fof(f549,plain,(
% 14.13/2.19    r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3)),
% 14.13/2.19    inference(superposition,[],[f132,f125])).
% 14.13/2.19  fof(f132,plain,(
% 14.13/2.19    ( ! [X5] : (r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X5,sK3)) | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k4_xboole_0(sK2,X5),sK3)) )),
% 14.13/2.19    inference(superposition,[],[f87,f95])).
% 14.13/2.19  fof(f125,plain,(
% 14.13/2.19    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 14.13/2.19    inference(superposition,[],[f95,f69])).
% 14.13/2.19  fof(f64,plain,(
% 14.13/2.19    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 14.13/2.19    inference(cnf_transformation,[],[f31])).
% 14.13/2.19  fof(f31,plain,(
% 14.13/2.19    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 14.13/2.19    inference(ennf_transformation,[],[f10])).
% 14.13/2.19  fof(f10,axiom,(
% 14.13/2.19    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 14.13/2.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 14.13/2.19  fof(f56,plain,(
% 14.13/2.19    sK1 != sK3 | sK0 != sK2),
% 14.13/2.19    inference(cnf_transformation,[],[f37])).
% 14.13/2.19  fof(f31337,plain,(
% 14.13/2.19    sK1 = sK3),
% 14.13/2.19    inference(forward_demodulation,[],[f31336,f61])).
% 14.13/2.19  fof(f31336,plain,(
% 14.13/2.19    sK3 = k4_xboole_0(sK1,k1_xboole_0)),
% 14.13/2.19    inference(forward_demodulation,[],[f31326,f26802])).
% 14.13/2.19  fof(f31326,plain,(
% 14.13/2.19    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK3)),
% 14.13/2.19    inference(superposition,[],[f81,f31270])).
% 14.13/2.19  fof(f31270,plain,(
% 14.13/2.19    k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 14.13/2.19    inference(subsumption_resolution,[],[f31263,f54])).
% 14.13/2.19  fof(f31263,plain,(
% 14.13/2.19    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 14.13/2.19    inference(trivial_inequality_removal,[],[f31262])).
% 14.13/2.19  fof(f31262,plain,(
% 14.13/2.19    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 14.13/2.19    inference(superposition,[],[f57,f28082])).
% 14.13/2.19  % SZS output end Proof for theBenchmark
% 14.13/2.19  % (4008)------------------------------
% 14.13/2.19  % (4008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.13/2.19  % (4008)Termination reason: Refutation
% 14.13/2.19  
% 14.13/2.19  % (4008)Memory used [KB]: 11769
% 14.13/2.19  % (4008)Time elapsed: 1.737 s
% 14.13/2.19  % (4008)------------------------------
% 14.13/2.19  % (4008)------------------------------
% 14.13/2.19  % (3989)Success in time 1.819 s
%------------------------------------------------------------------------------
