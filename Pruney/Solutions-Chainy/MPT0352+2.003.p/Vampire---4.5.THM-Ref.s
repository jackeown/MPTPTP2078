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
% DateTime   : Thu Dec  3 12:44:14 EST 2020

% Result     : Theorem 3.18s
% Output     : Refutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 340 expanded)
%              Number of leaves         :   25 (  97 expanded)
%              Depth                    :   22
%              Number of atoms          :  226 ( 628 expanded)
%              Number of equality atoms :   49 ( 187 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5519,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5518,f1290])).

fof(f1290,plain,(
    r1_tarski(k3_subset_1(sK0,sK2),sK0) ),
    inference(superposition,[],[f81,f1285])).

fof(f1285,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f85,f45])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f53,f59])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f5518,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f5517,f1396])).

fof(f1396,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f1395,f1303])).

fof(f1303,plain,(
    ! [X1] :
      ( r1_xboole_0(k3_subset_1(sK0,sK2),X1)
      | ~ r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f1292,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1292,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k3_subset_1(sK0,sK2))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f86,f1285])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f59])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f1395,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f1358,f43])).

fof(f43,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f1358,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_subset_1(sK0,sK1))
      | r1_xboole_0(X1,sK1) ) ),
    inference(superposition,[],[f87,f1286])).

fof(f1286,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f85,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f74,f59])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f5517,plain,
    ( ~ r1_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | ~ r1_tarski(k3_subset_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f5491,f1375])).

fof(f1375,plain,(
    ! [X3] :
      ( r1_tarski(X3,k3_subset_1(sK0,sK1))
      | ~ r1_xboole_0(X3,sK1)
      | ~ r1_tarski(X3,sK0) ) ),
    inference(superposition,[],[f89,f1286])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f59])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f5491,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f5489,f44])).

fof(f44,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f5489,plain,(
    r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f5482,f166])).

fof(f166,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f164,f91])).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f164,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f160,f47])).

fof(f47,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f160,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f64,f46])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f5482,plain,
    ( ~ r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f5445,f1398])).

fof(f1398,plain,(
    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f1396,f66])).

fof(f5445,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k3_subset_1(sK0,sK2))
      | ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f90,f5436])).

fof(f5436,plain,(
    sK0 = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f1834,f5434])).

fof(f5434,plain,(
    sK0 = k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f1296,f5433])).

fof(f5433,plain,(
    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK2)) ),
    inference(forward_demodulation,[],[f5398,f102])).

fof(f102,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f79,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f55,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f50,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f5398,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f1094,f5017])).

fof(f5017,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f4980,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f4980,plain,(
    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f4952,f55])).

fof(f4952,plain,(
    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f167,f222])).

fof(f222,plain,(
    ! [X2] : r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)),sK0) ),
    inference(resolution,[],[f203,f81])).

fof(f203,plain,(
    ! [X19] :
      ( ~ r1_tarski(X19,sK2)
      | r1_tarski(X19,sK0) ) ),
    inference(resolution,[],[f76,f165])).

fof(f165,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f163,f91])).

fof(f163,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f159,f47])).

fof(f159,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f64,f45])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)
      | v1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(resolution,[],[f65,f80])).

fof(f80,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f1094,plain,(
    ! [X2,X1] : k3_tarski(k1_enumset1(X2,X2,X1)) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(superposition,[],[f83,f55])).

fof(f83,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f58,f78,f59])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1296,plain,(
    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK0,sK0,sK2)) ),
    inference(forward_demodulation,[],[f1291,f82])).

fof(f82,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f54,f56,f56])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1291,plain,(
    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f83,f1285])).

fof(f1834,plain,(
    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1833,f1296])).

fof(f1833,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1826,f82])).

fof(f1826,plain,(
    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) ),
    inference(superposition,[],[f84,f1285])).

fof(f84,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f60,f78,f59,f78])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:52:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.46  % (22487)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.46  % (22471)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.48  % (22476)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.48  % (22484)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.49  % (22468)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.49  % (22469)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (22467)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (22485)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (22463)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (22477)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (22473)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (22475)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (22465)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (22486)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (22479)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (22488)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (22492)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (22480)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (22472)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (22470)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (22491)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (22481)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (22464)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.52  % (22478)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.52  % (22466)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.53  % (22489)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.53  % (22483)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.54  % (22490)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.55  % (22474)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.55  % (22482)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 3.18/0.77  % (22469)Refutation found. Thanks to Tanya!
% 3.18/0.77  % SZS status Theorem for theBenchmark
% 3.18/0.77  % SZS output start Proof for theBenchmark
% 3.18/0.77  fof(f5519,plain,(
% 3.18/0.77    $false),
% 3.18/0.77    inference(subsumption_resolution,[],[f5518,f1290])).
% 3.18/0.77  fof(f1290,plain,(
% 3.18/0.77    r1_tarski(k3_subset_1(sK0,sK2),sK0)),
% 3.18/0.77    inference(superposition,[],[f81,f1285])).
% 3.18/0.77  fof(f1285,plain,(
% 3.18/0.77    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 3.18/0.77    inference(resolution,[],[f85,f45])).
% 3.18/0.77  fof(f45,plain,(
% 3.18/0.77    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.18/0.77    inference(cnf_transformation,[],[f27])).
% 3.18/0.77  fof(f27,plain,(
% 3.18/0.77    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.18/0.77    inference(ennf_transformation,[],[f26])).
% 3.18/0.77  fof(f26,negated_conjecture,(
% 3.18/0.77    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.18/0.77    inference(negated_conjecture,[],[f25])).
% 3.18/0.77  fof(f25,conjecture,(
% 3.18/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 3.18/0.77  fof(f85,plain,(
% 3.18/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 3.18/0.77    inference(definition_unfolding,[],[f67,f59])).
% 3.18/0.77  fof(f59,plain,(
% 3.18/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.18/0.77    inference(cnf_transformation,[],[f4])).
% 3.18/0.77  fof(f4,axiom,(
% 3.18/0.77    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.18/0.77  fof(f67,plain,(
% 3.18/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f34])).
% 3.18/0.77  fof(f34,plain,(
% 3.18/0.77    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.18/0.77    inference(ennf_transformation,[],[f23])).
% 3.18/0.77  fof(f23,axiom,(
% 3.18/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 3.18/0.77  fof(f81,plain,(
% 3.18/0.77    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.18/0.77    inference(definition_unfolding,[],[f53,f59])).
% 3.18/0.77  fof(f53,plain,(
% 3.18/0.77    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f8])).
% 3.18/0.77  fof(f8,axiom,(
% 3.18/0.77    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.18/0.77  fof(f5518,plain,(
% 3.18/0.77    ~r1_tarski(k3_subset_1(sK0,sK2),sK0)),
% 3.18/0.77    inference(subsumption_resolution,[],[f5517,f1396])).
% 3.18/0.77  fof(f1396,plain,(
% 3.18/0.77    r1_xboole_0(k3_subset_1(sK0,sK2),sK1)),
% 3.18/0.77    inference(subsumption_resolution,[],[f1395,f1303])).
% 3.18/0.77  fof(f1303,plain,(
% 3.18/0.77    ( ! [X1] : (r1_xboole_0(k3_subset_1(sK0,sK2),X1) | ~r1_tarski(X1,sK2)) )),
% 3.18/0.77    inference(resolution,[],[f1292,f66])).
% 3.18/0.77  fof(f66,plain,(
% 3.18/0.77    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f33])).
% 3.18/0.77  fof(f33,plain,(
% 3.18/0.77    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.18/0.77    inference(ennf_transformation,[],[f3])).
% 3.18/0.77  fof(f3,axiom,(
% 3.18/0.77    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 3.18/0.77  fof(f1292,plain,(
% 3.18/0.77    ( ! [X0] : (r1_xboole_0(X0,k3_subset_1(sK0,sK2)) | ~r1_tarski(X0,sK2)) )),
% 3.18/0.77    inference(superposition,[],[f86,f1285])).
% 3.18/0.77  fof(f86,plain,(
% 3.18/0.77    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.18/0.77    inference(definition_unfolding,[],[f72,f59])).
% 3.18/0.77  fof(f72,plain,(
% 3.18/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 3.18/0.77    inference(cnf_transformation,[],[f35])).
% 3.18/0.77  fof(f35,plain,(
% 3.18/0.77    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.18/0.77    inference(ennf_transformation,[],[f15])).
% 3.18/0.77  fof(f15,axiom,(
% 3.18/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 3.18/0.77  fof(f1395,plain,(
% 3.18/0.77    r1_xboole_0(k3_subset_1(sK0,sK2),sK1) | r1_tarski(sK1,sK2)),
% 3.18/0.77    inference(resolution,[],[f1358,f43])).
% 3.18/0.77  fof(f43,plain,(
% 3.18/0.77    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 3.18/0.77    inference(cnf_transformation,[],[f27])).
% 3.18/0.77  fof(f1358,plain,(
% 3.18/0.77    ( ! [X1] : (~r1_tarski(X1,k3_subset_1(sK0,sK1)) | r1_xboole_0(X1,sK1)) )),
% 3.18/0.77    inference(superposition,[],[f87,f1286])).
% 3.18/0.77  fof(f1286,plain,(
% 3.18/0.77    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 3.18/0.77    inference(resolution,[],[f85,f46])).
% 3.18/0.77  fof(f46,plain,(
% 3.18/0.77    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.18/0.77    inference(cnf_transformation,[],[f27])).
% 3.18/0.77  fof(f87,plain,(
% 3.18/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_xboole_0(X0,X2)) )),
% 3.18/0.77    inference(definition_unfolding,[],[f74,f59])).
% 3.18/0.77  fof(f74,plain,(
% 3.18/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f36])).
% 3.18/0.77  fof(f36,plain,(
% 3.18/0.77    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.18/0.77    inference(ennf_transformation,[],[f5])).
% 3.18/0.77  fof(f5,axiom,(
% 3.18/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 3.18/0.77  fof(f5517,plain,(
% 3.18/0.77    ~r1_xboole_0(k3_subset_1(sK0,sK2),sK1) | ~r1_tarski(k3_subset_1(sK0,sK2),sK0)),
% 3.18/0.77    inference(resolution,[],[f5491,f1375])).
% 3.18/0.77  fof(f1375,plain,(
% 3.18/0.77    ( ! [X3] : (r1_tarski(X3,k3_subset_1(sK0,sK1)) | ~r1_xboole_0(X3,sK1) | ~r1_tarski(X3,sK0)) )),
% 3.18/0.77    inference(superposition,[],[f89,f1286])).
% 3.18/0.77  fof(f89,plain,(
% 3.18/0.77    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.18/0.77    inference(definition_unfolding,[],[f75,f59])).
% 3.18/0.77  fof(f75,plain,(
% 3.18/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.18/0.77    inference(cnf_transformation,[],[f38])).
% 3.18/0.77  fof(f38,plain,(
% 3.18/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 3.18/0.77    inference(flattening,[],[f37])).
% 3.18/0.77  fof(f37,plain,(
% 3.18/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.18/0.77    inference(ennf_transformation,[],[f16])).
% 3.18/0.77  fof(f16,axiom,(
% 3.18/0.77    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 3.18/0.77  fof(f5491,plain,(
% 3.18/0.77    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 3.18/0.77    inference(resolution,[],[f5489,f44])).
% 3.18/0.77  fof(f44,plain,(
% 3.18/0.77    ~r1_tarski(sK1,sK2) | ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 3.18/0.77    inference(cnf_transformation,[],[f27])).
% 3.18/0.77  fof(f5489,plain,(
% 3.18/0.77    r1_tarski(sK1,sK2)),
% 3.18/0.77    inference(subsumption_resolution,[],[f5482,f166])).
% 3.18/0.77  fof(f166,plain,(
% 3.18/0.77    r1_tarski(sK1,sK0)),
% 3.18/0.77    inference(resolution,[],[f164,f91])).
% 3.18/0.77  fof(f91,plain,(
% 3.18/0.77    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 3.18/0.77    inference(equality_resolution,[],[f69])).
% 3.18/0.77  fof(f69,plain,(
% 3.18/0.77    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.18/0.77    inference(cnf_transformation,[],[f20])).
% 3.18/0.77  fof(f20,axiom,(
% 3.18/0.77    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 3.18/0.77  fof(f164,plain,(
% 3.18/0.77    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 3.18/0.77    inference(subsumption_resolution,[],[f160,f47])).
% 3.18/0.77  fof(f47,plain,(
% 3.18/0.77    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.18/0.77    inference(cnf_transformation,[],[f24])).
% 3.18/0.77  fof(f24,axiom,(
% 3.18/0.77    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 3.18/0.77  fof(f160,plain,(
% 3.18/0.77    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.18/0.77    inference(resolution,[],[f64,f46])).
% 3.18/0.77  fof(f64,plain,(
% 3.18/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f30])).
% 3.18/0.77  fof(f30,plain,(
% 3.18/0.77    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.18/0.77    inference(ennf_transformation,[],[f22])).
% 3.18/0.77  fof(f22,axiom,(
% 3.18/0.77    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 3.18/0.77  fof(f5482,plain,(
% 3.18/0.77    ~r1_tarski(sK1,sK0) | r1_tarski(sK1,sK2)),
% 3.18/0.77    inference(resolution,[],[f5445,f1398])).
% 3.18/0.77  fof(f1398,plain,(
% 3.18/0.77    r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 3.18/0.77    inference(resolution,[],[f1396,f66])).
% 3.18/0.77  fof(f5445,plain,(
% 3.18/0.77    ( ! [X0] : (~r1_xboole_0(X0,k3_subset_1(sK0,sK2)) | ~r1_tarski(X0,sK0) | r1_tarski(X0,sK2)) )),
% 3.18/0.77    inference(superposition,[],[f90,f5436])).
% 3.18/0.77  fof(f5436,plain,(
% 3.18/0.77    sK0 = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2)))),
% 3.18/0.77    inference(backward_demodulation,[],[f1834,f5434])).
% 3.18/0.77  fof(f5434,plain,(
% 3.18/0.77    sK0 = k5_xboole_0(sK2,k3_subset_1(sK0,sK2))),
% 3.18/0.77    inference(backward_demodulation,[],[f1296,f5433])).
% 3.18/0.77  fof(f5433,plain,(
% 3.18/0.77    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK2))),
% 3.18/0.77    inference(forward_demodulation,[],[f5398,f102])).
% 3.18/0.77  fof(f102,plain,(
% 3.18/0.77    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.18/0.77    inference(backward_demodulation,[],[f79,f96])).
% 3.18/0.77  fof(f96,plain,(
% 3.18/0.77    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.18/0.77    inference(superposition,[],[f55,f93])).
% 3.18/0.77  fof(f93,plain,(
% 3.18/0.77    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 3.18/0.77    inference(resolution,[],[f50,f52])).
% 3.18/0.77  fof(f52,plain,(
% 3.18/0.77    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f6])).
% 3.18/0.77  fof(f6,axiom,(
% 3.18/0.77    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.18/0.77  fof(f50,plain,(
% 3.18/0.77    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 3.18/0.77    inference(cnf_transformation,[],[f29])).
% 3.18/0.77  fof(f29,plain,(
% 3.18/0.77    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.18/0.77    inference(ennf_transformation,[],[f11])).
% 3.18/0.77  fof(f11,axiom,(
% 3.18/0.77    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 3.18/0.77  fof(f55,plain,(
% 3.18/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f1])).
% 3.18/0.77  fof(f1,axiom,(
% 3.18/0.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.18/0.77  fof(f79,plain,(
% 3.18/0.77    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.18/0.77    inference(definition_unfolding,[],[f48,f59])).
% 3.18/0.77  fof(f48,plain,(
% 3.18/0.77    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.18/0.77    inference(cnf_transformation,[],[f10])).
% 3.18/0.77  fof(f10,axiom,(
% 3.18/0.77    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 3.18/0.77  fof(f5398,plain,(
% 3.18/0.77    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0)),
% 3.18/0.77    inference(superposition,[],[f1094,f5017])).
% 3.18/0.77  fof(f5017,plain,(
% 3.18/0.77    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK0,sK2))),
% 3.18/0.77    inference(resolution,[],[f4980,f49])).
% 3.18/0.77  fof(f49,plain,(
% 3.18/0.77    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 3.18/0.77    inference(cnf_transformation,[],[f28])).
% 3.18/0.77  fof(f28,plain,(
% 3.18/0.77    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.18/0.77    inference(ennf_transformation,[],[f2])).
% 3.18/0.77  fof(f2,axiom,(
% 3.18/0.77    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 3.18/0.77  fof(f4980,plain,(
% 3.18/0.77    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK0,sK2)))),
% 3.18/0.77    inference(forward_demodulation,[],[f4952,f55])).
% 3.18/0.77  fof(f4952,plain,(
% 3.18/0.77    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))),
% 3.18/0.77    inference(resolution,[],[f167,f222])).
% 3.18/0.77  fof(f222,plain,(
% 3.18/0.77    ( ! [X2] : (r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)),sK0)) )),
% 3.18/0.77    inference(resolution,[],[f203,f81])).
% 3.18/0.77  fof(f203,plain,(
% 3.18/0.77    ( ! [X19] : (~r1_tarski(X19,sK2) | r1_tarski(X19,sK0)) )),
% 3.18/0.77    inference(resolution,[],[f76,f165])).
% 3.18/0.77  fof(f165,plain,(
% 3.18/0.77    r1_tarski(sK2,sK0)),
% 3.18/0.77    inference(resolution,[],[f163,f91])).
% 3.18/0.77  fof(f163,plain,(
% 3.18/0.77    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 3.18/0.77    inference(subsumption_resolution,[],[f159,f47])).
% 3.18/0.77  fof(f159,plain,(
% 3.18/0.77    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.18/0.77    inference(resolution,[],[f64,f45])).
% 3.18/0.77  fof(f76,plain,(
% 3.18/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f40])).
% 3.18/0.77  fof(f40,plain,(
% 3.18/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.18/0.77    inference(flattening,[],[f39])).
% 3.18/0.77  fof(f39,plain,(
% 3.18/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.18/0.77    inference(ennf_transformation,[],[f7])).
% 3.18/0.77  fof(f7,axiom,(
% 3.18/0.77    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.18/0.77  fof(f167,plain,(
% 3.18/0.77    ( ! [X0,X1] : (~r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) | v1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.18/0.77    inference(resolution,[],[f65,f80])).
% 3.18/0.77  fof(f80,plain,(
% 3.18/0.77    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.18/0.77    inference(definition_unfolding,[],[f51,f59])).
% 3.18/0.77  fof(f51,plain,(
% 3.18/0.77    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f14])).
% 3.18/0.77  fof(f14,axiom,(
% 3.18/0.77    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 3.18/0.77  fof(f65,plain,(
% 3.18/0.77    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f32])).
% 3.18/0.77  fof(f32,plain,(
% 3.18/0.77    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.18/0.77    inference(flattening,[],[f31])).
% 3.18/0.77  fof(f31,plain,(
% 3.18/0.77    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.18/0.77    inference(ennf_transformation,[],[f12])).
% 3.18/0.77  fof(f12,axiom,(
% 3.18/0.77    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 3.18/0.77  fof(f1094,plain,(
% 3.18/0.77    ( ! [X2,X1] : (k3_tarski(k1_enumset1(X2,X2,X1)) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) )),
% 3.18/0.77    inference(superposition,[],[f83,f55])).
% 3.18/0.77  fof(f83,plain,(
% 3.18/0.77    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.18/0.77    inference(definition_unfolding,[],[f58,f78,f59])).
% 3.18/0.77  fof(f78,plain,(
% 3.18/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.18/0.77    inference(definition_unfolding,[],[f57,f56])).
% 3.18/0.77  fof(f56,plain,(
% 3.18/0.77    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f19])).
% 3.18/0.77  fof(f19,axiom,(
% 3.18/0.77    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.18/0.77  fof(f57,plain,(
% 3.18/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.18/0.77    inference(cnf_transformation,[],[f21])).
% 3.18/0.77  fof(f21,axiom,(
% 3.18/0.77    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.18/0.77  fof(f58,plain,(
% 3.18/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.18/0.77    inference(cnf_transformation,[],[f17])).
% 3.18/0.77  fof(f17,axiom,(
% 3.18/0.77    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.18/0.77  fof(f1296,plain,(
% 3.18/0.77    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK0,sK0,sK2))),
% 3.18/0.77    inference(forward_demodulation,[],[f1291,f82])).
% 3.18/0.77  fof(f82,plain,(
% 3.18/0.77    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.18/0.77    inference(definition_unfolding,[],[f54,f56,f56])).
% 3.18/0.77  fof(f54,plain,(
% 3.18/0.77    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f18])).
% 3.18/0.77  fof(f18,axiom,(
% 3.18/0.77    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.18/0.77  fof(f1291,plain,(
% 3.18/0.77    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k5_xboole_0(sK2,k3_subset_1(sK0,sK2))),
% 3.18/0.77    inference(superposition,[],[f83,f1285])).
% 3.18/0.77  fof(f1834,plain,(
% 3.18/0.77    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2)))),
% 3.18/0.77    inference(forward_demodulation,[],[f1833,f1296])).
% 3.18/0.77  fof(f1833,plain,(
% 3.18/0.77    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2)))),
% 3.18/0.77    inference(forward_demodulation,[],[f1826,f82])).
% 3.18/0.77  fof(f1826,plain,(
% 3.18/0.77    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2)))),
% 3.18/0.77    inference(superposition,[],[f84,f1285])).
% 3.18/0.77  fof(f84,plain,(
% 3.18/0.77    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.18/0.77    inference(definition_unfolding,[],[f60,f78,f59,f78])).
% 3.18/0.77  fof(f60,plain,(
% 3.18/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f9])).
% 3.18/0.77  fof(f9,axiom,(
% 3.18/0.77    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.18/0.77  fof(f90,plain,(
% 3.18/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 3.18/0.77    inference(definition_unfolding,[],[f77,f78])).
% 3.18/0.77  fof(f77,plain,(
% 3.18/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 3.18/0.77    inference(cnf_transformation,[],[f42])).
% 3.18/0.77  fof(f42,plain,(
% 3.18/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.18/0.77    inference(flattening,[],[f41])).
% 3.18/0.77  fof(f41,plain,(
% 3.18/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 3.18/0.77    inference(ennf_transformation,[],[f13])).
% 3.18/0.77  fof(f13,axiom,(
% 3.18/0.77    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.18/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 3.18/0.77  % SZS output end Proof for theBenchmark
% 3.18/0.77  % (22469)------------------------------
% 3.18/0.77  % (22469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.18/0.77  % (22469)Termination reason: Refutation
% 3.18/0.77  
% 3.18/0.77  % (22469)Memory used [KB]: 8827
% 3.18/0.77  % (22469)Time elapsed: 0.354 s
% 3.18/0.77  % (22469)------------------------------
% 3.18/0.77  % (22469)------------------------------
% 3.18/0.77  % (22462)Success in time 0.422 s
%------------------------------------------------------------------------------
